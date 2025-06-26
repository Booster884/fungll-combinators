
module GLL.Combinators.Visit.First where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

data VarTerm t = Concrete (Maybe t) | First NTLabel | Follow NTLabel
    deriving (Eq, Ord, Show)
type NTLabel = String
type First t = S.Set (VarTerm t)
type Follow t = S.Set (VarTerm t)
type Env t = M.Map (VarTerm t) (S.Set (VarTerm t))
type Firsts t = M.Map NTLabel (S.Set (Maybe t))
type Res t = (Env t, First t, Follow t)
type Comb t = Env t -> NTLabel -> Res t

type First_Symb t = Comb t
type First_Choice t = Comb t
type First_Seq t = Comb t
type First_Alt t = Comb t

addToSet :: (Ord t) => VarTerm t -> First t -> Env t -> Env t
addToSet t ts env | t `M.member` env = M.adjust (`S.union` ts) t env
                  | otherwise        = M.insert t ts env

addDummy :: (Ord t) => NTLabel -> Env t -> Env t
addDummy label = M.union (M.fromList [ (First label, S.empty)
                                     , (Follow label, S.empty)])

first_nterm :: (Ord t) => NTLabel -> [First_Choice t] -> First_Symb t
first_nterm label = first_nterm' label . foldl first_alt first_fails

first_nterm' :: (Ord t) => NTLabel -> First_Choice t -> First_Symb t
first_nterm' label c env _ = if (First label) `M.member` env && (Follow label) `M.member` env
    then (env, first', follow')
    else let (env', first, follow) = c (addDummy label env) label
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
first_alt l r env nt = (env', lfst `S.union` rfst, lflw `S.union` rflw)
    where (le, lfst, lflw) = l env nt
          (re, rfst, rflw) = r le nt
          toModify = [Follow x | Follow x <- S.toList $ rflw `S.union` lflw]
          env' = foldr (`addToSet` S.singleton (Follow nt)) re toModify

-- Equivalent to epsilon
first_succeeds :: First_Seq t
first_succeeds env nt = (env, S.singleton $ Follow nt, S.empty)

first_fails :: First_Choice t
first_fails env _ = (env, S.empty, S.empty)

-- Starts combinator evaluation with empty environment.
constraints :: Comb t -> Env t
constraints c = (\(x, _, _) -> x) $ c M.empty ""

--------------------------------------------------------------------------------
-- Constraint solver
--------------------------------------------------------------------------------

-- Solve constraints to create a mapping from nonterminals to (concrete) first sets.
firsts :: (Ord t, Show t) => Env t -> NTLabel -> Firsts t
firsts env label = fromEnv $ solve env'
    where env' = addToSet (Follow label) (S.singleton $ Concrete Nothing) env

solve :: (Ord t) => Env t -> Env t
solve env = if env == env' then env' else solve env'
    where env' = addTransitives env

addTransitives :: (Ord t) => Env t -> Env t
addTransitives env = foldl addTransitive env (M.keys env)

addTransitive :: (Ord t) => Env t -> VarTerm t -> Env t
addTransitive env label = M.insert label newSet env
    where newSet = S.foldl' (\acc l -> acc `S.union` depsOf env l) oldSet oldSet
          oldSet = env M.! label

depsOf :: (Ord t) => Env t -> VarTerm t -> S.Set (VarTerm t)
depsOf _   (Concrete _) = S.empty
depsOf env label        = env M.! label

fromEnv :: (Ord t) => Env t -> Firsts t
fromEnv env = M.fromList [(nt, keepTerms ts) | (First nt, ts) <- M.toList env]
    where keepTerms ts = S.fromList $ mapMaybe concretise (S.toList ts)
          concretise (Concrete x) = Just x
          concretise _            = Nothing

-- tokenP :: t -> Comb t
-- tokenP = first_term . token'

token' :: t -> VarTerm t
token' = Concrete . Just
