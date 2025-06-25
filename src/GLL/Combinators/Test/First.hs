import GLL.Combinators.Visit.First
import Test.Hspec
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding (seq)

main :: IO ()
main = hspec $ do
    let nterm = first_nterm'
        alt = first_alt
        seq = first_seq
        succeeds = first_succeeds
        token = token'
    describe "basic grammar" $ do
        -- X ::= a | bc
        let fX = nterm "fX" (alt (tokenP 'a') (seq (tokenP 'b') (tokenP 'c')))
        it "generates correct constraints" $ do
            constraints fX `shouldBe`
                M.fromList [ (First  "fX", S.fromList [token 'a', token 'b'])
                           , (Follow "fX",S.fromList [])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fX) "fX" `shouldBe` M.fromList [("fX", S.fromList [Just 'a', Just 'b'])]
    describe "basic recursive grammar" $ do

        let fX = nterm "fX" (alt (tokenP 'a') (seq (tokenP 'a') fX))
        it "generates the correct constraints" $ do
            constraints fX `shouldBe`
                M.fromList [ (First  "fX", S.fromList [token 'a'])
                           , (Follow "fX", S.fromList [Follow "fX"])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fX) "fX" `shouldBe` M.fromList [("fX", S.fromList [Just 'a'])]
    describe "arithmetic grammar" $ do
        -- E ::= T + E | T
        -- T ::= F * T | F
        -- F ::= ( E ) | ident
        let fE = nterm "fE" $ alt (seq (seq fT (tokenP '+')) fE) fT
            fT = nterm "fT" $ alt (seq (seq fF (tokenP '*')) fT) fF
            fF = nterm "fF" $ alt (seq (tokenP '(') (seq fE (tokenP ')'))) (tokenP 'a')
        it "generates correct constraints" $ do
            constraints fE `shouldBe`
                M.fromList [ (First  "fE", S.fromList [First "fT"])
                           , (Follow "fE", S.fromList [token ')', Follow "fT", Follow "fE"])
                           , (First  "fT", S.fromList [First "fF"])
                           , (Follow "fT", S.fromList [token '+', Follow "fF", Follow "fT", Follow "fE"])
                           , (First  "fF", S.fromList [token '(', token 'a'])
                           , (Follow "fF", S.fromList [token '*', Follow "fT"])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fE) "fE" `shouldBe`
                M.fromList [ ("fE", S.fromList [Just '(', Just 'a'])
                           , ("fT", S.fromList [Just '(', Just 'a'])
                           , ("fF", S.fromList [Just '(', Just 'a'])
                           ]
    describe "compiler construction grammar" $ do
        -- Taken from Compiler Construction chapter 4
        -- S ::= L = R | R
        -- L ::= * R | ident
        -- R ::= L
        let fS = nterm "fS" $ alt (seq fL (seq (tokenP '=') fR)) fR
            fL = nterm "fL" $ alt (seq (tokenP '*') fR) (tokenP 'a')
            fR = nterm "fR" fL
        it "generates correct constraints" $ do
            constraints fS `shouldBe`
                M.fromList [ (First  "fS", S.fromList [First "fL", First "fR"])
                           , (Follow "fS", S.fromList [Follow "fR"])
                           , (First  "fL", S.fromList [token '*', token 'a'])
                           , (Follow "fL", S.fromList [Follow "fR", token '='])
                           , (First  "fR", S.fromList [First "fL"])
                           , (Follow "fR", S.fromList [Follow "fS", Follow "fL"])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fS) "fS" `shouldBe`
                M.fromList [ ("fS", S.fromList [Just '*', Just 'a'])
                           , ("fL", S.fromList [Just '*', Just 'a'])
                           , ("fR", S.fromList [Just '*', Just 'a'])
                           ]
    describe "empty alternate" $ do
        -- E ::= e E | epsilon
        let fE = nterm "fE" $ alt (seq (tokenP 'e') fE) succeeds
        it "generates correct constraints" $ do
            constraints fE `shouldBe`
                M.fromList [ (First "fE",  S.fromList [token 'e', Follow "fE"])
                           , (Follow "fE", S.fromList [Follow "fE"])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fE) "fE" `shouldBe` M.fromList [("fE", S.fromList [Just 'e', Nothing])]
    describe "L&G grammar" $ do
        -- From Languages and Machines (Sudkamp 1988): G2 from section 15.1
        -- S ::= ABCabcd
        -- A ::= A | a
        -- B ::= B | b
        -- C ::= C | c
        let fS = nterm "fS" $ seq fA (seq fB (seq fC (seq (tokenP 'a') (seq (tokenP 'b') (seq (tokenP 'c') (tokenP 'd'))))))
            fA = nterm "fA" $ alt (tokenP 'a') succeeds
            fB = nterm "fB" $ alt (tokenP 'b') succeeds
            fC = nterm "fC" $ alt (tokenP 'c') succeeds
        it "generates correct constraints" $ do
            constraints fS `shouldBe`
                M.fromList [ (First "fS",  S.fromList [First "fA"])
                           , (Follow "fS", S.fromList [])
                           , (First "fA",  S.fromList [Follow "fA", token 'a'])
                           , (Follow "fA", S.fromList [First "fB"])
                           , (First "fB",  S.fromList [Follow "fB", token 'b'])
                           , (Follow "fB", S.fromList [First "fC"])
                           , (First "fC",  S.fromList [Follow "fC", token 'c'])
                           , (Follow "fC", S.fromList [token 'a'])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fS) "fS" `shouldBe`
                M.fromList [ ("fS", S.fromList [Just 'a', Just 'b', Just 'c'])
                           , ("fA", S.fromList [Just 'a', Just 'b', Just 'c'])
                           , ("fB", S.fromList [Just 'a', Just 'b', Just 'c'])
                           , ("fC", S.fromList [Just 'a', Just 'c'])
                           ]
    describe "left recursive grammar" $ do
        -- X ::= X a | epsilon
        let fX = nterm "fX" $ alt (seq fX (tokenP 'a')) succeeds
        it "generates correct constraints" $ do
            constraints fX `shouldBe`
                M.fromList [ (First "fX", S.fromList [First "fX", Follow "fX"])
                           , (Follow "fX", S.fromList [token 'a'])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fX) "fX" `shouldBe` M.fromList [("fX", S.fromList [Just 'a', Nothing])]
    describe "mutually recursive grammar" $ do
        -- M ::= N m | epsilon
        -- N ::= M n | epsilon
        let fM = nterm "fM" $ alt (seq fN (tokenP 'm')) succeeds
            fN = nterm "fN" $ alt (seq fM (tokenP 'n')) succeeds
        it "generates correct constraints" $ do
            constraints fM `shouldBe`
                M.fromList [ (First "fM",  S.fromList [First "fN", Follow "fM"])
                           , (Follow "fM", S.fromList [token 'n'])
                           , (First "fN",  S.fromList [First "fM", Follow "fN"])
                           , (Follow "fN", S.fromList [token 'm'])
                           ]
        it "generates correct first set" $ do
            firsts (constraints fM) "fM" `shouldBe`
                M.fromList [ ("fM", S.fromList [Just 'm', Just 'n', Nothing])
                           , ("fN", S.fromList [Just 'm', Just 'n', Nothing])
                           ]
    describe "nonterminal at end of alternate" $ do
        -- V ::= W | V 1
        -- W ::= z | epsilon
        let fV = nterm "fV" $ alt fW (seq fV (tokenP '1'))
            fW = nterm "fW" $ alt (tokenP 'z') succeeds
        it "works if nonterminal is at end of alternate" $ do
            constraints fV `shouldBe`
                M.fromList [ (First "fV",  S.fromList [First "fV", First "fW"])
                           , (Follow "fV", S.fromList [Follow "fW", token '1'])
                           , (First "fW", S.fromList  [Follow "fW", token 'z'])
                           , (Follow "fW", S.fromList [Follow "fV"])
                           ]
        it "is correct if nonterminal is at end of alternate" $ do
            firsts (constraints fV) "fV" `shouldBe`
                M.fromList [ ("fV", S.fromList [Just 'z', Just '1', Nothing])
                           , ("fW", S.fromList [Just 'z', Just '1', Nothing])
                           ]
