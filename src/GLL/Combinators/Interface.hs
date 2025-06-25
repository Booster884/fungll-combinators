{-# LANGUAGE TypeOperators, FlexibleInstances #-}

module GLL.Combinators.Interface (
    -- * Elementary parsers
    term_parser, satisfy,
    -- ** Elementary parsers using the 'Token' datatype 
    keychar, keyword, int_lit, float_lit, bool_lit, char_lit, string_lit, alt_id_lit, id_lit, token,
    -- ** Elementary character-level parsers
    char, 
    -- * Elementary combinators
    -- *** Sequencing
    (<**>),
    -- *** Choice
    (<||>),
    -- *** Semantic actions
    (<$$>), (<$$$>),
    -- *** Nonterminal introduction
    (<:=>),(<::=>),chooses,chooses_prec,
    -- *** Difference
    (<\\>),
    -- * Types
    -- ** Grammar (combinator expression) types
    BNF, SymbExpr, AltExpr, AltExprs,
    -- ** Parseable token types 
    Token(..), Parseable(..), SubsumesToken(..), unlexTokens, unlexToken,  
    -- * Running a parser 
    parse, printParseData, evaluatorWithParseData,
    -- **  Running a parser with options
    parseWithOptions, parseWithParseOptions, evaluatorWithParseDataAndOptions, 
    printParseDataWithOptions, 
    --printGrammarData,
    -- *** Possible options
    CombinatorOptions, CombinatorOption, 
             GLL.Combinators.Options.maximumErrors, throwErrors, 
             maximumPivot, maximumPivotAtNt,leftBiased,
    -- *** Running a parser with options and explicit failure
--    parseWithOptionsAndError, parseWithParseOptionsAndError,
    -- ** Runing a parser to obtain 'ParseResult'.
--    parseResult, parseResultWithOptions,ParseResult(..),
    -- ** Builtin lexers.
    default_lexer, 
    -- *** Lexer settings
        lexer, lexerEither, LexerSettings(..), emptyLanguage,
    -- * Derived combinators
    mkNt, 
    -- *** Ignoring semantic results
    (<$$), (**>), (<**),
    -- *** EBNF patterns
    optional, preferably, reluctantly, optionalWithDef,
    multiple, multiple1, multipleSepBy, multipleSepBy1,
      multipleSepBy2, within, parens, braces, brackets, angles,
      foldr_multiple, foldr_multipleSepBy,
    -- *** Operator expressions
    fromOpTable, opTableFromList, OpTable, Assoc(..), Fixity(..),
     -- *** Disambiguation  
            (<:=), (<::=),(<<<**>), (<**>>>), (<<**>), (<<<**), (**>>>), (<**>>),
            longest_match,shortest_match,
            many, many1, some, some1, 
            manySepBy, manySepBy1, manySepBy2, 
              someSepBy, someSepBy1,someSepBy2,
    -- * Lifting
    HasAlts(..), IsSymbExpr(..), IsAltExpr(..),
     -- * Memoisation
    memo, newMemoTable, memClear, MemoTable, MemoRef, useMemoisation,
     -- * Scannerless parsing, using `RawParser`s
    RawParser, lexical,
    ) where

import GLL.Combinators.Options
import GLL.Combinators.Visit.FUNGLL
import GLL.Combinators.Visit.First
import GLL.Combinators.Visit.Join
import GLL.Combinators.Visit.Sem
import GLL.Combinators.Memoisation
import GLL.Combinators.Lexer
import GLL.Types.Input
import GLL.Types.Grammar
import GLL.Types.TypeCompose
import GLL.Flags hiding (runOptions)
import GLL.Parseable.Char ()

import Control.Monad (when)
import Control.Arrow
import qualified Data.Array as A
import qualified Data.Map as M
import Data.Text (pack, unpack)
import Data.IORef 
import Data.Time.Clock
import System.IO.Unsafe

parse' :: (Show t, Parseable t, IsSymbExpr s) => ParseOptions -> 
            PCOptions -> s t a -> [t] -> (ParseResult t, Either String [a])
parse' popts opts p' input =  
    let SymbExpr (Nt lower_start, vpa2, vpa3, vpa4) =
          mkRule ("__Augment" <:=> OO [id <$$> p'])
        start       = pack "__Start"
        arr         = mkInput input 
        m           = length input 
        fsts        = firsts (constraints vpa4) "__Augment"
        parse_res   = parser_for start vpa2 arr fsts
        as          = evaluator_for lower_start vpa3 opts (bsrs_result parse_res) arr
        res_list    = unsafePerformIO as
    in (parse_res, if res_success parse_res && not (null res_list)
                    then Right $ res_list 
                    else Left (error_message parse_res) )
-- | Print some information about the parse.
-- Helpful for debugging.
printParseData :: (Parseable t, IsSymbExpr s, Show a) => s t a -> [t] -> IO ()
printParseData = printParseDataWithOptions [] [] 

-- | Variant of 'printParseData' which can be controlled by 'ParseOption's
printParseDataWithOptions :: (Parseable t, IsSymbExpr s, Show a) => ParseOptions -> CombinatorOptions -> s t a -> [t] -> IO ()
printParseDataWithOptions popts opts p' input = 
    let SymbExpr (Nt lower_start,vpa2,vpa3,vpa4) = toSymb p'
        start       = pack "__Start"
        fsts        = firsts (constraints vpa4) (unpack start)
        parse_res   = parser_for start vpa2 arr fsts
        arr         = mkInput input 
        m           = inputLength arr
    in do startTime <- getCurrentTime
          putStrLn $ "#tokens:              " ++ (show m)
          putStrLn $ "#successes:           " ++ (show $ res_successes parse_res)
          endTime <- getCurrentTime
          putStrLn $ "recognition time:     " ++ show (diffUTCTime endTime startTime)
          startTime' <- getCurrentTime
          putStrLn $ "#descriptors          " ++ (show $ nr_descriptors parse_res)
          putStrLn $ "#BSRs                 " ++ (show $ nr_bsrs parse_res) 
          endTime <- getCurrentTime
          putStrLn $ "parse-data time:      " ++ show (diffUTCTime endTime startTime')
          putStrLn $ "total time:           " ++ show (diffUTCTime endTime startTime)

-- | Print some information 
evaluatorWithParseData :: (Parseable t, IsSymbExpr s, Show a) => s t a -> [t] -> [a]
evaluatorWithParseData = evaluatorWithParseDataAndOptions [] [] 

evaluatorWithParseDataAndOptions :: (Parseable t, IsSymbExpr s, Show a) => ParseOptions -> CombinatorOptions -> s t a -> [t] -> [a]
evaluatorWithParseDataAndOptions popts opts p' input = 
    let SymbExpr (Nt lower_start,vpa2,vpa3,vpa4) = toSymb p'
        start       = pack "__Start"
        fsts        = firsts (constraints vpa4) (unpack start)
        parse_res   = parser_for start vpa2 arr fsts
        arr         = mkInput input 
        m           = inputLength arr
    in unsafePerformIO $ do 
          startTime <- getCurrentTime
          putStrLn $ "#tokens:              " ++ (show m)
          putStrLn $ "#successes:           " ++ (show $ res_successes parse_res)
          endTime <- getCurrentTime
          putStrLn $ "recognition time:     " ++ show (diffUTCTime endTime startTime)
          startTime' <- getCurrentTime
          putStrLn $ "#descriptors          " ++ (show $ nr_descriptors parse_res)
          putStrLn $ "#BSRs                 " ++ (show $ nr_bsrs parse_res) 
          endTime <- getCurrentTime
          putStrLn $ "parse-data time:      " ++ show (diffUTCTime endTime startTime')
          startTime' <- getCurrentTime
          as <- evaluator_for start vpa3 (runOptions opts) (bsrs_result parse_res) arr
--          putStrLn $ "#derivations:         " ++ show (length as)
          when (not (null as)) (writeFile "/tmp/derivation" (show (head as)))
          endTime <- getCurrentTime
          putStrLn $ "semantic phase:       " ++ show (diffUTCTime endTime startTime')
          putStrLn $ "total time:           " ++ show (diffUTCTime endTime startTime)
          return as
-- | 
-- Runs a parser given a string of 'Parseable's and returns a list of 
-- semantic results, corresponding to all finitely many derivations.
parse :: (Show t, Parseable t, IsSymbExpr s) => s t a -> [t] -> [a]
parse = parseWithOptions [throwErrors] 

-- | 
-- Run the parser with some 'CombinatorOptions'.
parseWithOptions :: (Show t, Parseable t, IsSymbExpr s) => 
                        CombinatorOptions -> s t a -> [t] -> [a]
parseWithOptions opts p ts = parseWithParseOptions defaultPOpts opts p ts

-- | 
-- Run the parser with some 'ParseOptions' and 'CombinatorOptions'.
parseWithParseOptions :: (Show t, Parseable t, IsSymbExpr s) => 
                     ParseOptions -> CombinatorOptions -> s t a -> [t] -> [a]
parseWithParseOptions pcopts opts p ts = 
    case parseWithParseOptionsAndError pcopts opts p ts of
        Left str | throw_errors opts'   -> error str
                 | otherwise            -> []
        Right as                        -> as
    where opts' = runOptions opts

-- | 
-- Run the parser with some 'CombinatorOptions' and return either an error or the results.
-- Any returned results will be a list of length greater than 0.
parseWithOptionsAndError :: (Show t, Parseable t, IsSymbExpr s) => 
                        CombinatorOptions -> s t a -> [t] -> Either String [a]
parseWithOptionsAndError opts p = parseWithParseOptionsAndError defaultPOpts opts p 

-- | 
-- Run the parser with some 'ParseOptions' and 'CombinatorOptions'.
-- Returns either an error or the results.
-- Any returned results will be a list of length greater than 0.
parseWithParseOptionsAndError :: (Show t, Parseable t, IsSymbExpr s) => 
       ParseOptions -> CombinatorOptions -> s t a -> [t] -> Either String [a]
parseWithParseOptionsAndError popts opts p = (\(_,t) -> t) . parse' defaultPOpts (runOptions opts) p


-- | Get the 'ParseResult', containing an 'SPPF', 
--  produced by parsing the given input with the given parser.
parseResult :: (Show t, Parseable t, IsSymbExpr s) => s t a -> [t] -> ParseResult t
parseResult = parseResultWithOptions [] [] 

-- | Get the 'ParseResult' given some 'ParseOptions' and 'CombinatorOptions'. 
parseResultWithOptions :: (Show t, Parseable t, IsSymbExpr s) => 
         ParseOptions -> CombinatorOptions -> s t a -> [t] -> ParseResult t
parseResultWithOptions popts opts p str = 
    (\(s,_) -> s) $ parse' popts (runOptions opts) p str

defaultPOpts = [strictBinarisation, packedNodesOnly]

infixl 2 <:=>
-- | 
-- Form a rule by giving the name of the left-hand side of the new rule.
-- Use this combinator on recursive non-terminals.
(<:=>) :: (Show t, Ord t, Parseable t, HasAlts b) => String -> b t a -> SymbExpr t a
x <:=> altPs = mkNtRule False False x altPs
infixl 2 <::=>

-- | 
--  Variant of '<:=>' for recursive non-terminals that have a potentially infinite
--  number of derivations for some input string.
--
--  A non-terminal yields infinitely many derivations  
--  if and only if it is left-recursive and would be
--  left-recursive if all the right-hand sides of the productions of the
--  grammar are reversed.
(<::=>) :: (Show t, Ord t, Parseable t, HasAlts b) => String -> b t a -> SymbExpr t a
x <::=> altPs = mkNtRule True False x altPs

-- | Variant of '<::=>' that can be supplied with a list of alternates
chooses :: (Show t, Ord t, Parseable t, IsAltExpr alt) => String -> [alt t a] -> SymbExpr t a
chooses p alts | null alts = error "chooses cannot be given an empty list of alternatives"
               | otherwise = (<::=>) p (OO (map toAlt alts))

-- | Variant of '<::=' that can be supplied with a list of alternates
chooses_prec :: (Show t, Ord t, Parseable t, IsAltExpr alt) => String -> [alt t a] -> SymbExpr t a
chooses_prec p alts | null alts = error "chooses cannot be given an empty list of alternatives"
                    | otherwise = (<::=) p (OO (map toAlt alts))

infixl 4 <$$>
-- |
-- Form an 'AltExpr' by mapping some semantic action overy the result
-- of the second argument.
(<$$>) :: (Show t, Ord t, Parseable t, IsSymbExpr s) => (a -> b) -> s t a -> AltExpr t b
f <$$> p' = join_apply ((:[]) . f) p'

infixl 4 <$$$>
-- | 
-- Variant of `<$$>` that gives access to the underlying ambiguity representation
-- The semantic action can be used to disambiguate, for example using `guard`.
(<$$$>) :: (Show t, Ord t, Parseable t, IsSymbExpr s, Foldable f) => (a -> f b) -> s t a -> AltExpr t b
f <$$$> p' = join_apply f p'


infixl 4 <**>,<<<**>,<**>>>
-- | 
-- Add a 'SymbExpr' to the right-hand side represented by an 'AltExpr'
-- creating a new 'AltExpr'. 
-- The semantic result of the first argument is applied to the second 
-- as a cross-product. 
(<**>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) =>
            i t (a -> b) -> s t a -> AltExpr t b
pl' <**> pr' = join_seq [] pl' pr'

-- | Variant of '<**>' that applies longest match on the left operand.
(<**>>>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) =>
            i t (a -> b) -> s t a -> AltExpr t b
pl' <**>>> pr' = join_seq [maximumPivot] pl' pr'

-- | Variant of '<**>' that applies shortest match on the left operand.
(<<<**>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) =>
            i t (a -> b) -> s t a -> AltExpr t b
pl' <<<**> pr' = join_seq [minimumPivot] pl' pr'


infixr 5 <\\>
(<\\>) :: (Show t) => SymbExpr t a -> SymbExpr t b -> SymbExpr t a
p <\\> q = p `join_andNot` q

infixr 3 <||>
-- |
-- Add an 'AltExpr' to a list of 'AltExpr'
-- The resuling  '[] :. AltExpr' forms the right-hand side of a rule.
(<||>) :: (Show t, Ord t, Parseable t, IsAltExpr i, HasAlts b) => i t a -> b t a -> AltExprs t a
l' <||> r' = let l = toAlt l'
                 r = altsOf r'
             in OO (l : r)

-- |
-- Apply this combinator to an alternative to turn all underlying occurrences
-- of '<**>' (or variants) apply 'longest match'.
longest_match :: (Show t, Ord t, Parseable t, IsAltExpr alt) => alt t a -> AltExpr t a
longest_match isalt = AltExpr (v1,v2,\opts -> v3 (maximumPivot opts),v4)
  where AltExpr (v1,v2,v3,v4) = toAlt isalt

-- Apply this combinator to an alternative to turn all underlying occurrences
-- of '<**>' (or variants) apply 'shortest match'.
shortest_match :: (Show t, Ord t, Parseable t, IsAltExpr alt) => alt t a -> AltExpr t a
shortest_match isalt = AltExpr (v1,v2,\opts -> v3 (minimumPivot opts),v4)
  where AltExpr (v1,v2,v3,v4) = toAlt isalt

-- | Create a symbol-parse for a terminal given:
--
--  * The 'Parseable' token represented by the terminal.
--  * A function from that 'Parseable' to a semantic result.
term_parser :: Parseable t => t -> (t -> a) -> SymbExpr t a 
term_parser t f = SymbExpr (Term t, parse_term t,\_ _ _ inp l _ -> return [f (fst inp A.! l)],first_term $ token' t)

-- | Create a symbol given a `RawParser` (see `GLL.Types.Input`)
lexical :: String -> RawParser t -> SymbExpr t [t]
lexical nt regex = join_lexical (pack nt) regex

-- | Parse a single character.
--
-- @
-- char c = term_parser c id
-- @
--
-- Currently, this is the only character-level combinator exported
-- by this module. Please use token-level combinators for practical parsing.
-- Might change in the future.
char :: Char -> SymbExpr Char Char
char c = term_parser c id
{-
-- | Parse a list of characters.
string :: [Char] -> SymbExpr Char [Char]
string [] = mkRule $ satisfy []
string (c:cs) = mkRule $ (:) <$$> char c <**> string cs

-- | 
-- Apply a parser within two other parsers.
within :: IsSymbExpr s => BNF Char a -> s Char b -> BNF Char c -> BNF Char b
within l p r = mkRule $ l *> (toSymb p) <* r

-- | 
-- Apply a parser within parentheses.
-- parens p = within (char '(') p (char ')')
parens :: BNF Char a -> BNF Char a 
parens p = within (char '(') p (char ')')
-}

-- | Parse a single character, using a 'SubsumesToken' type.
keychar :: (Parseable t, SubsumesToken t) => Char -> SymbExpr t Char
keychar c = term_parser (upcast (Char c)) (const c)        -- helper for Char tokens

-- | Parse a single character, using a 'SubsumesToken' type.
keyword :: (Parseable t, SubsumesToken t) => String -> SymbExpr t String
keyword k = term_parser (upcast (Keyword k)) (const k)        -- helper for Char tokens

-- | Parse a single integer, using a 'SubsumesToken' type.
-- Returns the lexeme interpreted as an 'Int'.
int_lit :: (Parseable t, SubsumesToken t) => SymbExpr t Int
int_lit  = term_parser (upcast (IntLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (IntLit (Just i)))  = i
        unwrap _ = error "int_lit: downcast, or token without lexeme"

-- | Parse a single floating point literal, using a 'SubsumesToken' type.
-- Returns the lexeme interpreted as a 'Double'.
float_lit :: (Parseable t, SubsumesToken t) => SymbExpr t Double
float_lit  = term_parser (upcast (FloatLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (FloatLit (Just i)))  = i
        unwrap _ = error "float_lit: downcast, or token without lexeme"

-- | Parse a single Boolean, using a 'SubsumesToken' type.
-- Returns the lexeme interpreter as a Boolean.
bool_lit :: (Parseable t, SubsumesToken t) => SymbExpr t Bool
bool_lit  = term_parser (upcast (BoolLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (BoolLit (Just b)))  = b
        unwrap _ = error "bool_lit: downcast, or token without lexeme"

-- | Parse a single Character literal, using a 'SubsumesToken' type.
-- Returns the lexeme interpreted as a Character literal.
char_lit :: (Parseable t, SubsumesToken t) => SymbExpr t Char
char_lit  = term_parser (upcast (CharLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (CharLit (Just s))) = s
        unwrap _ = error "char_lit: downcast, or token without lexeme"

-- | Parse a single String literal, using a 'SubsumesToken' type.
-- Returns the lexeme interpreted as a String literal.
string_lit :: (Parseable t, SubsumesToken t) => SymbExpr t String
string_lit  = term_parser (upcast (StringLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (StringLit (Just i))) = i
        unwrap _ = error "string_lit: downcast, or token without lexeme"

-- | Parse a single identifier, using a 'SubsumesToken' type.
-- Returns the lexeme as a String.
id_lit :: (Parseable t, SubsumesToken t) => SymbExpr t String
id_lit = term_parser (upcast (IDLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (IDLit (Just i))) = i
        unwrap _ = error "id_lit: downcast, or token without lexeme"

-- | Parse a single alternative identifier, using a 'SubsumesToken' type.
-- Returns the lexeme as a String.
alt_id_lit :: (Parseable t, SubsumesToken t) => SymbExpr t String
alt_id_lit = term_parser (upcast (AltIDLit Nothing)) (unwrap . downcast)
 where  unwrap (Just (AltIDLit (Just i))) = i
        unwrap _ = error "alt_id_lit: downcast, or token without lexeme"


-- | Parse a single arbitrary token, using a 'SubsumesToken' type.
-- Returns the lexeme.
token :: (Parseable t, SubsumesToken t) => String -> SymbExpr t String
token name = term_parser (upcast (Token name Nothing)) (unwrap . downcast)
 where  unwrap (Just (Token name' (Just i))) | name == name' = i
        unwrap _  = error "tokenT: downcast, or token without lexeme"

epsilon :: (Show t, Ord t) => AltExpr t ()
epsilon = AltExpr ([], seqStart ,\_ _ _ _ _ l r -> 
                        if l == r then return [(l,())] else return []
                     , first_succeeds)
    where x = "__eps"

-- | The empty right-hand side that yields its 
--  first argument as a semantic result.
satisfy :: (Show t, Ord t, Parseable t) => a -> AltExpr t a
satisfy a = a <$$ epsilon

-- | 
-- This function memoises a parser, given:
--
-- * A 'MemoRef' pointing to a fresh 'MemoTable', created using 'newMemoTable'.
-- * The 'SymbExpr' to memoise.
--
-- Use 'memo' on those parsers that are expected to derive the same 
-- substring multiple times. If the same combinator expression is used
-- to parse multiple times the 'MemoRef' needs to be cleared using 'memClear'.
--
-- 'memo' relies on 'unsafePerformIO' and is therefore potentially unsafe.
-- The option 'useMemoisation' enables memoisation.
-- It is off by default, even if 'memo' is used in a combinator expression.
memo :: (Ord t, Show t, Parseable t, IsSymbExpr s) => MemoRef [a] -> s t a -> SymbExpr t a
memo ref p' = let   SymbExpr (sym,rules,sem,first) = toSymb p'
                    lhs_sem opts ctx sppf arr l r 
                        | not (do_memo opts) = sem opts ctx sppf arr l r
                        | otherwise = do
                            tab <- readIORef ref
                            case memLookup (l,r) tab of
                                Just as -> return as
                                Nothing -> do   as <- sem opts ctx sppf arr l r
                                                modifyIORef ref (memInsert (l,r) as)
                                                return as
               in SymbExpr (sym, rules, lhs_sem, first)

-- | 
-- Helper function for defining new combinators.
-- Use 'mkNt' to form a new unique non-terminal name based on
-- the symbol of a given 'SymbExpr' and a 'String' that is unique to
-- the newly defined combinator.
mkNt :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> String -> String
mkNt p str = let SymbExpr (myx,_,_,_) = mkRule p
                in "_(" ++ show  myx ++ ")" ++ str

-- | Specialised fmap for altparsers
(.$.) :: (Show t, Ord t, Parseable t, IsAltExpr i) => (a -> b) -> i t a -> AltExpr t b
f .$. i = let AltExpr (s,r,sem,first) = toAlt i
            in AltExpr (s,r,\opts slot ctx sppf arr l r -> 
                                do  as <- sem opts slot ctx sppf arr l r
                                    return $ map (id *** f) as , first)

-- | 
-- Variant of '<$$>' that ignores the semantic result of its second argument. 
(<$$) :: (Show t, Ord t, Parseable t, IsSymbExpr s) => b -> s t a -> AltExpr t b
f <$$ p = const f <$$> p
infixl 4 <$$

-- | 
infixl 4 **>, <<**>, **>>>

-- | 
-- Variant of '<**>' that ignores the semantic result of the first argument.
(**>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t b
l **> r = flip const .$. l <**> r

-- Variant of '<**>' that applies longest match on its left operand. 
(**>>>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t b
l **>>> r = flip const .$. l <**>>> r

-- Variant of '<**>' that ignores shortest match on its left operand.
(<<**>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t b
l <<**>r = flip const .$. l <<<**> r


infixl 4 <**, <<<**, <**>>
-- | 
-- Variant of '<**>' that ignores the semantic result of the second argument.
(<**) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t a
l <** r = const .$. l <**> r 

-- | Variant of '<**' that applies longest match on its left operand.
(<**>>) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t a
l <**>> r = const .$. l <**>>> r 

-- | Variant '<**' that applies shortest match on its left operand
(<<<**) :: (Show t, Ord t, Parseable t, IsAltExpr i, IsSymbExpr s) => i t a -> s t b -> AltExpr t a
l <<<** r = const .$. l <<<**> r 

-- | 
-- Variant of '<::=>' that prioritises productions from left-to-right (or top-to-bottom).
x <::= altPs = mkNtRule True True x altPs 
infixl 2 <::=

-- | 
-- Variant of '<:=>' that prioritises productions from left-to-right (or top-to-bottom).
x <:= altPs = mkNtRule False True x altPs 
infixl 2 <:=

-- | Try to apply a parser multiple times (0 or more) with shortest match
-- applied to each occurrence of the parser.
many :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
many = multiple_ (<<<**>)

-- | Try to apply a parser multiple times (1 or more) with shortest match
-- applied to each occurrence of the parser.
many1 :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
many1 = multiple1_ (<<<**>) 

-- | Try to apply a parser multiple times (0 or more) with longest match
-- applied to each occurrence of the parser.
some :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
some = multiple_ (<**>>>)

-- | Try to apply a parser multiple times (1 or more) with longest match
-- applied to each occurrence of the parser.
some1 :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
some1 = multiple1_ (<**>>>) 

-- | Try to apply a parser multiple times (0 or more). The results are returned in a list.
-- In the case of ambiguity the largest list is returned.
multiple :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
multiple = multiple_ (<**>)

-- | Try to apply a parser multiple times (1 or more). The results are returned in a list.
-- In the case of ambiguity the largest list is returned.
multiple1 :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t [a]
multiple1 = multiple1_ (<**>)

-- | Internal
multiple_ disa p = let fresh = mkNt p "*" 
                    in fresh <::=> ((:) <$$> p) `disa` (multiple_ disa p) <||> satisfy []

-- | Internal
multiple1_ disa p = let fresh = mkNt p "+"
                     in fresh <::=> ((:) <$$> p) `disa` (multiple_ disa p)

-- | Same as 'many' but with an additional separator.
manySepBy :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                s t a -> s2 t b -> SymbExpr t [a]
manySepBy = sepBy many
-- | Same as 'many1' but with an additional separator.
manySepBy1 :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                s t a -> s2 t b -> SymbExpr t [a]
manySepBy1 = sepBy1 many
-- | Same as 'some1' but with an additional separator.
someSepBy :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                s t a -> s2 t b -> SymbExpr t [a]
someSepBy = sepBy some
-- | Same as 'some1' but with an additional separator.
someSepBy1 :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                s t a -> s2 t b -> SymbExpr t [a]
someSepBy1 = sepBy1 some
-- | Same as 'multiple' but with an additional separator.
multipleSepBy :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                    s t a -> s2 t b -> SymbExpr t [a]
multipleSepBy = sepBy multiple 
-- | Same as 'multiple1' but with an additional separator.
multipleSepBy1 :: (Show t, Ord t, Parseable t, IsSymbExpr s, IsSymbExpr s2, IsAltExpr s2) =>
                    s t a -> s2 t b -> SymbExpr t [a]
multipleSepBy1 = sepBy1 multiple 

sepBy :: (Show t, Ord t, Parseable t, IsSymbExpr s1, IsSymbExpr s2, IsAltExpr s2) =>
           (AltExpr t a -> SymbExpr t [a]) -> s1 t a -> s2 t b -> SymbExpr t [a]
sepBy mult p c = mkRule $ satisfy [] <||> (:) <$$> p <**> mult (c **> p)

sepBy1 :: (Show t, Ord t, Parseable t, IsSymbExpr s1, IsSymbExpr s2, IsAltExpr s2) =>
           (AltExpr t a -> SymbExpr t [a]) -> s1 t a -> s2 t b -> SymbExpr t [a]
sepBy1 mult p c = mkRule $ (:) <$$> p <**> mult (c **> p)

-- | Like 'multipleSepBy1' but matching at least two occurrences of the 
-- first argument. The returned list is therefore always of at least
-- length 2. At least one separator will be consumed.
multipleSepBy2 p s = mkRule $
  (:) <$$> p <** s <**> multipleSepBy1 p s

-- | Like 'multipleSepBy2' but matching the minimum number of 
-- occurrences of the first argument as possible (at least 2).
someSepBy2 p s = mkRule $
  (:) <$$> p <** s <**> someSepBy1 p s

-- | Like 'multipleSepBy2' but matching the maximum number of
-- occurrences of the first argument as possible (at least 2).
manySepBy2 p s = mkRule $ 
  (:) <$$> p <** s <**> manySepBy1 p s

-- | Derive either from the given symbol or the empty string.
optional :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t (Maybe a)
optional p = fresh 
  <:=>  Just <$$> p 
  <||>  satisfy Nothing 
  where fresh = mkNt p "?"

-- | Version of 'optional' that prefers to derive from the given symbol,
-- affects only nullable nonterminal symbols
preferably :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t (Maybe a)
preferably p = fresh 
  <:=   Just <$$> p 
  <||>  satisfy Nothing 
  where fresh = mkNt p "?"

-- | Version of 'optional' that prefers to derive the empty string from 
-- the given symbol, affects only nullable nonterminal symbols
reluctantly :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> SymbExpr t (Maybe a)
reluctantly p = fresh 
  <:=   satisfy Nothing  
  <||>  Just <$$> p
  where fresh = mkNt p "?"

optionalWithDef :: (Show t, Ord t, Parseable t, IsSymbExpr s) => s t a -> a -> SymbExpr t a
optionalWithDef p def = mkNt p "?" <:=> id <$$> p <||> satisfy def

-- | Place a piece of BNF /within/ two other BNF fragments, ignoring their semantics.
within :: (Show t, Ord t, Parseable t, IsSymbExpr s) => BNF t a -> s t b -> BNF t c -> BNF t b
within l p r = mkRule $ l **> toSymb p <** r

-- | Place a piece of BNF between the characters '(' and ')'.
parens p = within (keychar '(') p (keychar ')')
-- | Place a piece of BNF between the characters '{' and '}'.
braces p = within (keychar '{') p (keychar '}')
-- | Place a piece of BNF between the characters '[' and ']'.
brackets p = within (keychar '[') p (keychar ']')
-- | Place a piece of BNF between the characters '<' and '>'.
angles p = within (keychar '<') p (keychar '>')
-- | Place a piece of BNF between two single quotes.
quotes p = within (keychar '\'') p (keychar '\'')
-- | Place a piece of BNF between two double quotes.
dquotes p = within (keychar '"') p (keychar '"')

foldr_multiple :: (IsSymbExpr s, Parseable t) => s t (a -> a) -> a -> BNF t a
foldr_multiple comb def = mkNt comb "-foldr" 
  <::=> satisfy def 
  <||> ($)      <$$> comb <<<**> foldr_multiple comb def

foldr_multipleSepBy :: (IsSymbExpr s, Parseable t) => s t (a -> a) -> s t b -> a -> BNF t a
foldr_multipleSepBy comb sep def = mkNt comb "-foldr" 
  <::=> satisfy def 
  <||>  ($ def) <$$> comb
  <||> ($)      <$$> comb <** sep <<<**> foldr_multipleSepBy comb sep def

-- | A table mapping operator keywords to a 'Fixity' and 'Assoc'
-- It provides a convenient way to build an expression grammar (see 'fromOpTable'). 
type OpTable e  = M.Map Double [(String, Fixity e)] 
data Fixity e   = Prefix (String -> e -> e) | Infix (e -> String -> e -> e) Assoc
data Assoc      = LAssoc | RAssoc | NA

opTableFromList :: [(Double, [(String, Fixity e)])] -> OpTable e 
opTableFromList = M.fromList

fromOpTable :: (SubsumesToken t, Parseable t, IsSymbExpr s) => String -> OpTable e -> s t e -> BNF t e 
fromOpTable nt ops rec = chooses_prec (nt ++ "-infix-prefix-exprs") $
  [ mkNterm ix row
  | (ix, row) <- zip [1..] (M.elems ops)
  ]
  where mkNterm ix ops = chooses (ntName ix) $ 
          [ mkAlt op fix | (op, fix) <- ops ]
          where mkAlt op fix = case fix of
                  Prefix f -> f <$$> keyword op <**> rec 
                  Infix f assoc -> case assoc of 
                    LAssoc -> f <$$> rec <**> keyword op <**>>> rec
                    RAssoc -> f <$$> rec <**> keyword op <<<**> rec
                    _      -> f <$$> rec <**> keyword op <**> rec
                
        ntName i = show i ++ nt ++ "-op-row"

