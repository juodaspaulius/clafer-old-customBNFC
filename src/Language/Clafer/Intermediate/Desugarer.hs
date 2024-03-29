{-# LANGUAGE RankNTypes #-}
{-
 Copyright (C) 2012 Kacper Bak, Jimmy Liang <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
{- | Transforms an Abstract Syntax Tree (AST) from "Language.Clafer.Front.Absclafer"
into Intermediate representation (IR) from "Language.Clafer.Intermediate.Intclafer" of a Clafer model.
-}
module Language.Clafer.Intermediate.Desugarer where

import Language.Clafer.Common
import Language.Clafer.Front.Absclafer
import Language.Clafer.Intermediate.Intclafer

-- | Transform the AST into the intermediate representation (IR)
desugarModule :: Module -> IModule
desugarModule (Module _ declarations) = IModule "" $
      declarations >>= desugarEnums >>= desugarDeclaration
--      [ImoduleFragment $ declarations >>= desugarEnums >>= desugarDeclaration]

sugarModule :: IModule -> Module
sugarModule x = Module noSpan $ map sugarDeclaration $ _mDecls x -- (fragments x >>= mDecls)

-- | desugars enumeration to abstract and global singleton features
desugarEnums :: Declaration -> [Declaration]
desugarEnums (EnumDecl s id' enumids) = absEnum : map mkEnum enumids
    where
    oneToOne = (CardInterval noSpan $ NCard noSpan (PosInteger ((0,0), "1")) (ExIntegerNum noSpan $ PosInteger ((0,0), "1")))
    absEnum = ElementDecl s $ Subclafer noSpan $ Clafer noSpan
              (Abstract noSpan) (GCardEmpty noSpan) id' (SuperEmpty noSpan) (CardEmpty noSpan)
              (InitEmpty noSpan) (ElementsList noSpan [])
    mkEnum (EnumIdIdent s' eId) = ElementDecl s' $ Subclafer s' $ Clafer s' (AbstractEmpty noSpan) (GCardEmpty noSpan)
                                  eId ((SuperSome noSpan) (SuperColon noSpan) (ClaferId noSpan $ Path noSpan [ModIdIdent noSpan id']))
                                  oneToOne (InitEmpty noSpan) (ElementsList noSpan [])
desugarEnums x = [x]


desugarDeclaration :: Declaration -> [IElement]
desugarDeclaration (ElementDecl _ element) = desugarElement element
desugarDeclaration _ = error "desugared"


sugarDeclaration :: IElement -> Declaration
sugarDeclaration (IEClafer clafer) = ElementDecl noSpan $ Subclafer noSpan $ sugarClafer clafer
sugarDeclaration (IEConstraint True constraint) =
      (ElementDecl noSpan) $ Subconstraint noSpan $ sugarConstraint constraint
sugarDeclaration  (IEConstraint False softconstraint) =
      (ElementDecl noSpan) $ Subsoftconstraint noSpan $ sugarSoftConstraint softconstraint
sugarDeclaration  (IEGoal _ goal) = ElementDecl noSpan $ Subgoal noSpan $ sugarGoal goal


desugarClafer :: Clafer -> [IElement]
desugarClafer (Clafer s abstract gcrd id' super' crd init' es)  =
    (IEClafer $ IClafer s (desugarAbstract abstract) (desugarGCard gcrd) (transIdent id')
            "" (desugarSuper super') (desugarCard crd) (0, -1)
            (desugarElements es)) : (desugarInit id' init')


sugarClafer :: IClafer -> Clafer
sugarClafer (IClafer _ abstract gcard' _ uid' super' crd _ es) =
    Clafer noSpan (sugarAbstract abstract) (sugarGCard gcard') (mkIdent uid')
      (sugarSuper super') (sugarCard crd) (InitEmpty noSpan) (sugarElements es)


desugarSuper :: Super -> ISuper
desugarSuper (SuperEmpty s) =
      ISuper False [PExp (Just $ TClafer []) "" s $ mkLClaferId baseClafer True]
desugarSuper (SuperSome _ superhow setexp) =
      ISuper (desugarSuperHow superhow) [desugarSetExp setexp]


desugarSuperHow :: SuperHow -> Bool
desugarSuperHow (SuperColon _) = False
desugarSuperHow _  = True


desugarInit :: Ident -> Init -> [IElement]
desugarInit _ (InitEmpty _) = []
desugarInit id' (InitSome s inithow exp') = [IEConstraint (desugarInitHow inithow)
  (pExpDefPid s (IFunExp "=" [mkPLClaferId (snd $ getIdent id') False, desugarExp exp']))]
  where getIdent (PosIdent y) = y

desugarInitHow :: InitHow -> Bool
desugarInitHow (InitHow_1 _) = True
desugarInitHow (InitHow_2 _ )= False


desugarName :: Name -> IExp
desugarName (Path _ path) =
      IClaferId (concatMap ((++ modSep).desugarModId) (init path))
                (desugarModId $ last path) True

desugarModId :: ModId -> Result
desugarModId (ModIdIdent _ id') = transIdent id'

sugarModId :: String -> ModId
sugarModId modid = ModIdIdent noSpan $ mkIdent modid

sugarSuper :: ISuper -> Super
sugarSuper (ISuper _ []) = SuperEmpty noSpan
sugarSuper (ISuper isOverlapping' [pexp]) = SuperSome noSpan (sugarSuperHow isOverlapping') (sugarSetExp pexp)
sugarSuper _ = error "Function sugarSuper from Desugarer expects an ISuper with a list of length one, but it was given one with a list larger than one" -- Should never happen

sugarSuperHow :: Bool -> SuperHow
sugarSuperHow False = SuperColon noSpan
sugarSuperHow True  = SuperMArrow noSpan


sugarInitHow :: Bool -> InitHow
sugarInitHow True  = InitHow_1 noSpan
sugarInitHow False = InitHow_2 noSpan


desugarConstraint :: Constraint -> PExp
desugarConstraint (Constraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'

desugarSoftConstraint :: SoftConstraint -> PExp
desugarSoftConstraint (SoftConstraint _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'

desugarGoal :: Goal -> PExp
desugarGoal (Goal _ exps') = desugarPath $ desugarExp $
    (if length exps' > 1 then foldl1 (EAnd noSpan) else head) exps'

sugarConstraint :: PExp -> Constraint
sugarConstraint pexp = Constraint noSpan $ map sugarExp [pexp]

sugarSoftConstraint :: PExp -> SoftConstraint
sugarSoftConstraint pexp = SoftConstraint noSpan $ map sugarExp [pexp]

sugarGoal :: PExp -> Goal
sugarGoal pexp = Goal noSpan $ map sugarExp [pexp]

desugarAbstract :: Abstract -> Bool
desugarAbstract (AbstractEmpty _) = False
desugarAbstract (Abstract _) = True


sugarAbstract :: Bool -> Abstract
sugarAbstract False = AbstractEmpty noSpan
sugarAbstract True = Abstract noSpan


desugarElements :: Elements -> [IElement]
desugarElements (ElementsEmpty _) = []
desugarElements (ElementsList _ es)  = es >>= desugarElement


sugarElements :: [IElement] -> Elements
sugarElements x = ElementsList noSpan $ map sugarElement x


desugarElement :: Element -> [IElement]
desugarElement x = case x of
  Subclafer _ claf  ->
      (desugarClafer claf) ++
      (mkArrowConstraint claf >>= desugarElement)
  ClaferUse s name crd es  -> desugarClafer $ Clafer s
      (AbstractEmpty noSpan) (GCardEmpty noSpan) (mkIdent $ _sident $ desugarName name)
      (SuperSome noSpan (SuperColon noSpan) (ClaferId noSpan name)) crd (InitEmpty noSpan) es
  Subconstraint _ constraint  ->
      [IEConstraint True $ desugarConstraint constraint]
  Subsoftconstraint _ softconstraint ->
      [IEConstraint False $ desugarSoftConstraint softconstraint]
  Subgoal _ goal -> [IEGoal True $ desugarGoal goal]

sugarElement :: IElement -> Element
sugarElement x = case x of
  IEClafer claf  -> Subclafer noSpan $ sugarClafer claf
  IEConstraint True constraint -> Subconstraint noSpan $ sugarConstraint constraint
  IEConstraint False softconstraint -> Subsoftconstraint noSpan $ sugarSoftConstraint softconstraint
  IEGoal _ goal -> Subgoal noSpan $ sugarGoal goal

mkArrowConstraint :: Clafer -> [Element]
mkArrowConstraint (Clafer _ _ _ ident' super' _ _ _) =
  if isSuperSomeArrow super' then  [Subconstraint noSpan $
       Constraint noSpan [DeclAllDisj noSpan
       (Decl noSpan [LocIdIdent noSpan $ mkIdent "x", LocIdIdent noSpan $ mkIdent "y"]
             (ClaferId noSpan  $ Path noSpan [ModIdIdent noSpan ident']))
       (ENeq noSpan (ESetExp noSpan $ Join noSpan (ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent "x"])
                             (ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent "ref"]))
             (ESetExp noSpan $ Join noSpan (ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent "y"])
                             (ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent "ref"])))]]
  else []

isSuperSomeArrow :: Super -> Bool
isSuperSomeArrow (SuperSome _ arrow _) = isSuperArrow arrow
isSuperSomeArrow _ = False

isSuperArrow :: SuperHow -> Bool
isSuperArrow (SuperArrow _) = True
isSuperArrow _ = False

desugarGCard :: GCard -> Maybe IGCard
desugarGCard x = case x of
  GCardEmpty _  -> Nothing
  GCardXor _ -> Just $ IGCard True (1, 1)
  GCardOr _  -> Just $ IGCard True (1, -1)
  GCardMux _ -> Just $ IGCard True (0, 1)
  GCardOpt _ -> Just $ IGCard True (0, -1)
  GCardInterval _ ncard ->
      Just $ IGCard (isOptionalDef ncard) $ desugarNCard ncard

isOptionalDef :: NCard -> Bool
isOptionalDef (NCard _ m n) = ((0::Integer) == mkInteger m) && (not $ isExIntegerAst n)

isExIntegerAst :: ExInteger -> Bool
isExIntegerAst (ExIntegerAst _) = True
isExIntegerAst _ = False

sugarGCard :: Maybe IGCard -> GCard
sugarGCard x = case x of
  Nothing -> GCardEmpty noSpan
  Just (IGCard _ (i, ex)) -> GCardInterval noSpan $ NCard noSpan (PosInteger ((0, 0), show i)) (sugarExInteger ex)


desugarCard :: Card -> Maybe Interval
desugarCard x = case x of
  CardEmpty _  -> Nothing
  CardLone _  ->  Just (0, 1)
  CardSome _  ->  Just (1, -1)
  CardAny _ ->  Just (0, -1)
  CardNum _ n  -> Just (mkInteger n, mkInteger n)
  CardInterval _ ncard  -> Just $ desugarNCard ncard

desugarNCard :: NCard -> (Integer, Integer)
desugarNCard (NCard _ i ex) = (mkInteger i, desugarExInteger ex)

desugarExInteger :: ExInteger -> Integer
desugarExInteger (ExIntegerAst _) = -1
desugarExInteger (ExIntegerNum _ n) = mkInteger n

sugarCard :: Maybe Interval -> Card
sugarCard x = case x of
  Nothing -> CardEmpty noSpan
  Just (i, ex) ->
      CardInterval noSpan $ NCard noSpan (PosInteger ((0, 0), show i)) (sugarExInteger ex)

sugarExInteger :: Integer -> ExInteger
sugarExInteger n = if n == -1 then ExIntegerAst noSpan else (ExIntegerNum noSpan $ PosInteger ((0, 0), show n))

desugarExp :: Exp -> PExp
desugarExp x = pExpDefPid (getSpan x) $ desugarExp' x

desugarExp' :: Exp -> IExp
desugarExp' x = case x of
  DeclAllDisj _ decl exp' ->
      IDeclPExp IAll [desugarDecl True decl] (dpe exp')
  DeclAll _ decl exp' -> IDeclPExp IAll [desugarDecl False decl] (dpe exp')
  DeclQuantDisj _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl True decl] (dpe exp')
  DeclQuant _ quant' decl exp' ->
      IDeclPExp (desugarQuant quant') [desugarDecl False decl] (dpe exp')
  EIff _ exp0 exp'  -> dop iIff [exp0, exp']
  EImplies _ exp0 exp'  -> dop iImpl [exp0, exp']
  EImpliesElse _ exp0 exp1 exp'  -> dop iIfThenElse [exp0, exp1, exp']
  EOr _ exp0 exp'  -> dop iOr   [exp0, exp']
  EXor _ exp0 exp'  -> dop iXor [exp0, exp']
  EAnd _ exp0 exp'  -> dop iAnd [exp0, exp']
  ENeg _ exp'  -> dop iNot [exp']
  QuantExp _ quant' exp' ->
      IDeclPExp (desugarQuant quant') [] (desugarExp exp')
  ELt  _ exp0 exp'  -> dop iLt  [exp0, exp']
  EGt  _ exp0 exp'  -> dop iGt  [exp0, exp']
  EEq  _ exp0 exp'  -> dop iEq  [exp0, exp']
  ELte _ exp0 exp'  -> dop iLte [exp0, exp']
  EGte _ exp0 exp'  -> dop iGte [exp0, exp']
  ENeq _ exp0 exp'  -> dop iNeq [exp0, exp']
  EIn  _ exp0 exp'  -> dop iIn  [exp0, exp']
  ENin _ exp0 exp'  -> dop iNin [exp0, exp']
  EAdd _ exp0 exp'  -> dop iPlus [exp0, exp']
  ESub _ exp0 exp'  -> dop iSub [exp0, exp']
  EMul _ exp0 exp'  -> dop iMul [exp0, exp']
  EDiv _ exp0 exp'  -> dop iDiv [exp0, exp']
  ECSetExp _ exp'   -> dop iCSet [exp']
  ESumSetExp _ exp' -> dop iSumSet [exp']
  EMinExp _ exp'    -> dop iMin [exp']
  EGMax _ exp' -> dop iGMax [exp']
  EGMin _ exp' -> dop iGMin [exp']
  EInt _ n  -> IInt $ mkInteger n
  EDouble _ (PosDouble n) -> IDouble $ read $ snd n
  EStr _ (PosString str)  -> IStr $ snd str
  ESetExp _ sexp -> desugarSetExp' sexp
  where
  dop = desugarOp desugarExp
  dpe = desugarPath.desugarExp

desugarOp :: (a -> PExp) -> String -> [a] -> IExp
desugarOp f op' exps' =
    if (op' == iIfThenElse)
      then IFunExp op' $ (desugarPath $ head mappedList) : (map reducePExp $ tail mappedList)
      else IFunExp op' $ map (trans.f) exps'
    where
      mappedList = map f exps'
      trans = if op' `elem` ([iNot, iIfThenElse] ++ logBinOps)
          then desugarPath else id


desugarSetExp :: SetExp -> PExp
desugarSetExp x = pExpDefPid (getSpan x) $ desugarSetExp' x


desugarSetExp' :: SetExp -> IExp
desugarSetExp' x = case x of
  Union _ exp0 exp'        -> dop iUnion        [exp0, exp']
  UnionCom _ exp0 exp'     -> dop iUnion        [exp0, exp']
  Difference _ exp0 exp'   -> dop iDifference   [exp0, exp']
  Intersection _ exp0 exp' -> dop iIntersection [exp0, exp']
  Domain _ exp0 exp'       -> dop iDomain       [exp0, exp']
  Range _ exp0 exp'        -> dop iRange        [exp0, exp']
  Join _ exp0 exp'         -> dop iJoin         [exp0, exp']
  ClaferId _ name  -> desugarName name

  where
  dop = desugarOp desugarSetExp


sugarExp :: PExp -> Exp
sugarExp x = sugarExp' $ Language.Clafer.Intermediate.Intclafer._exp x


sugarExp' :: IExp -> Exp
sugarExp' x = case x of
  IDeclPExp quant' [] pexp -> QuantExp noSpan (sugarQuant quant') (sugarExp pexp)
  IDeclPExp IAll (decl@(IDecl True _ _):[]) pexp ->
    DeclAllDisj noSpan  (sugarDecl decl) (sugarExp pexp)
  IDeclPExp IAll  (decl@(IDecl False _ _):[]) pexp ->
    DeclAll noSpan (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl True _ _):[]) pexp ->
    DeclQuantDisj noSpan (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IDeclPExp quant' (decl@(IDecl False _ _):[]) pexp ->
    DeclQuant noSpan  (sugarQuant quant') (sugarDecl decl) (sugarExp pexp)
  IFunExp op' exps' ->
    if op' `elem` unOps then (sugarUnOp op') noSpan (exps''!!0)
    else if op' `elem` setBinOps then (ESetExp noSpan $ sugarSetExp' x)
    else if op' `elem` binOps then (sugarOp op') noSpan (exps''!!0) (exps''!!1)
    else (sugarTerOp op') noSpan (exps''!!0) (exps''!!1) (exps''!!2)
    where
    exps'' = map sugarExp exps'
  IInt n -> EInt noSpan $ PosInteger ((0, 0), show n)
  IDouble n -> EDouble noSpan $ PosDouble ((0, 0), show n)
  IStr str -> EStr noSpan $ PosString ((0, 0), str)
  IClaferId _ _ _ -> ESetExp noSpan $ sugarSetExp' x
  _ -> error "Function sugarExp' from Desugarer was given an invalid argument" -- This should never happen
  where
  sugarUnOp op''
    | op'' == iNot           = ENeg
    | op'' == iCSet          = ECSetExp
    | op'' == iMin           = EMinExp
    | op'' == iGMax          = EGMax
    | op'' == iGMin          = EGMin
    | op'' == iSumSet        = ESumSetExp
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarOp op''
    | op'' == iIff           = EIff
    | op'' == iImpl          = EImplies
    | op'' == iOr            = EOr
    | op'' == iXor           = EXor
    | op'' == iAnd           = EAnd
    | op'' == iLt            = ELt
    | op'' == iGt            = EGt
    | op'' == iEq            = EEq
    | op'' == iLte           = ELte
    | op'' == iGte           = EGte
    | op'' == iNeq           = ENeq
    | op'' == iIn            = EIn
    | op'' == iNin           = ENin
    | op'' == iPlus          = EAdd
    | op'' == iSub           = ESub
    | op'' == iMul           = EMul
    | op'' == iDiv           = EDiv
    | otherwise            = error $ show op'' ++ "is not an op"
  sugarTerOp op''
    | op'' == iIfThenElse    = EImpliesElse
    | otherwise            = error $ show op'' ++ "is not an op"


sugarSetExp :: PExp -> SetExp
sugarSetExp x = sugarSetExp' $ Language.Clafer.Intermediate.Intclafer._exp x


sugarSetExp' :: IExp -> SetExp
sugarSetExp' (IFunExp op' exps') = (sugarOp op' noSpan) (exps''!!0) (exps''!!1)
    where
    exps'' = map sugarSetExp exps'
    sugarOp op''
      | op'' == iUnion         = Union
      | op'' == iDifference    = Difference
      | op'' == iIntersection  = Intersection
      | op'' == iDomain        = Domain
      | op'' == iRange         = Range
      | op'' == iJoin          = Join
      | otherwise              = error "Invalid argument given to function sygarSetExp' in Desugarer"
sugarSetExp' (IClaferId "" id' _) = ClaferId noSpan $ Path noSpan [ModIdIdent noSpan $ mkIdent id']
sugarSetExp' (IClaferId modName' id' _) = ClaferId noSpan $ Path noSpan $ (sugarModId modName') : [sugarModId id']
sugarSetExp' _ = error "IDecelPexp, IInt, IDobule, and IStr can not be sugared into a setExp!" --This should never happen

desugarPath :: PExp -> PExp
desugarPath (PExp iType' pid' pos' x) = reducePExp $ PExp iType' pid' pos' result
  where
  result
    | isSet x     = IDeclPExp ISome [] (pExpDefPid pos' x)
    | isNegSome x = IDeclPExp INo   [] $ _bpexp $ Language.Clafer.Intermediate.Intclafer._exp $ head $ _exps x
    | otherwise   =  x
  isNegSome (IFunExp op' [PExp _ _ _ (IDeclPExp ISome [] _)]) = op' == iNot
  isNegSome _ = False


isSet :: IExp -> Bool
isSet (IClaferId _ _ _)  = True
isSet (IFunExp op' _) = op' `elem` setBinOps
isSet _ = False


-- reduce parent
reducePExp :: PExp -> PExp
reducePExp (PExp t pid' pos' x) = PExp t pid' pos' $ reduceIExp x

reduceIExp :: IExp -> IExp
reduceIExp (IDeclPExp quant' decls' pexp) = IDeclPExp quant' decls' $ reducePExp pexp
reduceIExp (IFunExp op' exps') = redNav $ IFunExp op' $ map redExps exps'
    where
    (redNav, redExps) = if op' == iJoin then (reduceNav, id) else (id, reducePExp)
reduceIExp x = x

reduceNav :: IExp -> IExp
reduceNav x@(IFunExp op' exps'@((PExp _ _ _ iexp@(IFunExp _ (pexp0:pexp:_))):pPexp:_)) =
  if op' == iJoin && isParent pPexp && isClaferName pexp
  then reduceNav $ Language.Clafer.Intermediate.Intclafer._exp pexp0
  else x{_exps = (head exps'){Language.Clafer.Intermediate.Intclafer._exp = reduceIExp iexp} :
                tail exps'}
reduceNav x = x


desugarDecl :: Bool -> Decl -> IDecl
desugarDecl isDisj' (Decl _ locids exp') =
    IDecl isDisj' (map desugarLocId locids) (desugarSetExp exp')


sugarDecl :: IDecl -> Decl
sugarDecl (IDecl _ locids exp') =
    Decl noSpan (map sugarLocId locids) (sugarSetExp exp')


desugarLocId :: LocId -> String
desugarLocId (LocIdIdent _ id') = transIdent id'


sugarLocId :: String -> LocId
sugarLocId x = LocIdIdent noSpan $ mkIdent x

desugarQuant :: Quant -> IQuant
desugarQuant (QuantNo _) = INo
desugarQuant (QuantLone _) = ILone
desugarQuant (QuantOne _) = IOne
desugarQuant (QuantSome _) = ISome

sugarQuant :: IQuant -> Quant
sugarQuant INo = QuantNo noSpan
sugarQuant ILone = QuantLone noSpan
sugarQuant IOne = QuantOne noSpan
sugarQuant ISome = QuantSome noSpan
sugarQuant IAll = error "sugarQaunt was called on IAll, this is not allowed!" --Should never happen
