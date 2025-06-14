
module GLL.Combinators.Visit.First where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Prelude hiding (seq)

data VarTerm t = Concrete (Maybe t) | First NTLabel | Follow NTLabel
    deriving (Eq, Ord, Show)
type NTLabel = String
type First t = S.Set (VarTerm t)
type Follow t = S.Set (VarTerm t)
type Env t = M.Map (VarTerm t) (S.Set (VarTerm t))
type Firsts t = M.Map NTLabel (First t)
type Res t = (Env t, First t, Follow t)
type Comb t = Env t -> NTLabel -> Res t

type First_Symb t = Comb t
type First_Choice t = Comb t
type First_Seq t = Comb t
type First_Alt t = Comb t

addToSet :: (Ord t) => VarTerm t -> First t -> Env t -> Env t
addToSet t ts = M.adjust (`S.union` ts) t

addDummy :: (Ord t) => NTLabel -> Env t -> Env t
addDummy label = M.union (M.fromList [ (First label, S.empty)
                                     , (Follow label, S.empty)])

first_nterm :: (Ord t) => NTLabel -> [First_Choice t] -> First_Symb t
first_nterm  label = first_nterm' label . foldl first_alt first_fails

first_nterm' :: (Ord t) => NTLabel -> First_Choice t -> First_Symb t
first_nterm' label c env _ = case (M.lookup (First label) env, M.lookup (Follow label) env) of
    (Just _, Just _) -> (env, first', follow')
    _ -> let (env', first, follow) = c (addDummy label env) label
             env'' = addToSet (First label) first (addToSet (Follow label) follow env')
         in (env'', first', follow')
    where first' = S.singleton $ First label
          follow' = S.singleton $ Follow label

first_term :: VarTerm t -> First_Symb t
first_term t env _ = (env, S.singleton t, S.empty)

first_seq :: (Ord t) => First_Seq t -> First_Symb t -> First_Seq t
first_seq l r env nt = (env', lfst, rflw)
    where (re, rfst, rflw) = r env nt
          (le, lfst, lflw) = l re nt
          toModify = [Follow x | Follow x <- S.toList lflw]
          env' = foldr (`addToSet` rfst) le toModify

first_alt :: (Ord t) => First_Choice t -> First_Seq t -> First_Choice t
first_alt l r env nt = (re, lfst `S.union` rfst, lflw `S.union` rflw)
    where (le, lfst, lflw) = l env nt
          (re, rfst, rflw) = r le nt

-- Equivalent to epsilon
first_succeeds :: First_Seq t
first_succeeds env nt = (env, S.singleton $ Follow nt, S.empty)

-- TODO: Not quite sure what this represents, EOF?
first_fails :: First_Choice t
first_fails env _ = (env, S.empty, S.empty)

-- Starts combinator evaluation with empty environment.
constraints :: Comb t -> Env t
constraints c = (\(x, _, _) -> x) $ c M.empty ""

--------------------------------------------------------------------------------
-- Constraint solver
--------------------------------------------------------------------------------

-- Solve constraints to create a mapping from nonterminals to (concrete) first sets.
firsts :: (Ord t) => Env t -> NTLabel -> M.Map NTLabel (S.Set (Maybe t))
firsts env label = fromEnv $ solve env' (First label)
    where env' = addToSet (Follow label) (S.singleton $ Concrete Nothing) env

solve :: (Ord t) => Env t -> VarTerm t -> Env t
solve env label = fst $ solve' env label

solve' :: (Ord t) => Env t -> VarTerm t -> (Env t, S.Set (VarTerm t))
solve' env label | null vars = (M.adjust (S.delete label) label env, toks)
                 | otherwise = let (env', symbs) = solve' env label'
                               in solve' (M.adjust (S.delete label' . S.union symbs) label env') label
                 where (vars, toks) = S.partition isVar $ S.delete label $ env M.! label
                       label' = head $ S.toList vars -- Only evaluated if vars is not empty

isVar :: VarTerm t -> Bool
isVar (First _)  = True
isVar (Follow _) = True
isVar _          = False

fromEnv :: (Ord t) => Env t -> M.Map NTLabel (S.Set (Maybe t))
-- HACK: Round trips through lists aren't great
fromEnv env = M.fromList [(nt, keepTerms ts) | (First nt, ts) <- M.toList env]
    where keepTerms ts = S.fromList $ fromMaybe [] $ mapM concretise (S.toList ts)
          concretise (Concrete x) = Just x
          concretise _            = Nothing

-- tokenP :: t -> Comb t
-- tokenP = first_term . token

token' :: t -> VarTerm t
token' = Concrete . Just
