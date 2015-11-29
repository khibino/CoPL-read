
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Writer
import Data.DList


data Nat
  = Z
  | S Nat
  deriving (Eq, Show)

data Op
  = Plus
  | Mult
  deriving (Eq, Show)

data Judge
  = Judge Op Nat Nat Nat
  deriving (Eq, Show)

data Rule
  = PZero
  | PSucc
  | TZero
  | TSucc
  deriving (Eq, Show)

data Derivation
  = By Judge (Rule, [Derivation])
  deriving (Eq, Show)

minus :: Nat -> Nat -> Maybe Nat
minus = d  where
  d  x     Z    = Just x
  d (S x) (S y) = minus x y
  d  Z     _    = Nothing

solve :: Judge -> Maybe Derivation
solve = d  where
  d x@(Judge Plus Z a b)
    | a == b     =   Just $ x `By` (PZero, [])
    | otherwise  =   Nothing
  d x@(Judge Plus (S n1) n2 (S n3))
    =             do a <- solve $ Judge Plus n1 n2 n3
                     Just $ x `By` (PSucc, [a])
  d (Judge Plus _ _ _)
    =                Nothing

  d x@(Judge Mult Z _ Z)
    =                Just $ x `By` (TZero, [])
  d x@(Judge Mult (S n1) n2 n4)
    =             do n3 <- minus n4 n2
                     a  <- solve $ Judge Mult n1 n2 n3
                     b  <- solve $ Judge Plus n2 n3 n4
                     Just $ x `By` (TSucc, [a, b])
  d (Judge Mult _ _ _)
    =                Nothing

q4 :: Judge
q4 = Judge Plus (S Z) (S (S (S Z))) (S (S (S (S Z))))


type Printer a = a -> Writer (DList Char) ()

runPrinter' :: Writer (DList Char) b -> String
runPrinter' = toList . execWriter

-- runPrinter :: Printer a -> a -> String
-- runPrinter p = runPrinter' . p

char :: Printer Char
char = tell . pure

string :: Printer String
string = mapM_ char

printNat :: Printer Nat
printNat = d  where
  d (S n) = do
    char 'S'
    char '('
    d n
    char ')'
  d  Z    =
    char 'Z'

printOp :: Printer Op
printOp = d  where
  d Plus  =  string "plus"
  d Mult  =  string "times"

printRule = d  where
  d PZero  =  string "P-Zero"
  d PSucc  =  string "P-Succ"
  d TZero  =  string "T-Zero"
  d TSucc  =  string "T-Succ"

printJudge :: Printer Judge
printJudge (Judge op n1 n2 n3) = do
  printNat n1
  char ' '
  printOp op
  char ' '
  printNat n2
  char ' '
  string "is"
  char ' '
  printNat n3

printDerivation :: Printer Derivation
printDerivation = rec' where
  rec' (By j (r, xs)) = do
    printJudge j
    char ' '
    string "by"
    char ' '
    printRule r
    char ' '
    list' xs
  list' (x:xs) = do
    char '{'
    char ' '
    printDerivation x
    forM_ xs $
      \y -> do
        char ';'
        char ' '
        printDerivation y
    char ' '
    char '}'
  list' []     = do
    char '{'
    char '}'

printD :: Derivation -> String
printD = runPrinter' . printDerivation

j2times2 :: Judge
j2times2 = Judge Mult (S (S Z)) (S (S Z)) (S (S (S (S Z))))

a4 :: Maybe String
a4 = printD <$> solve q4

-- Z times S(S(Z)) is Z
-- q5 = Judge Mult

main :: IO ()
main = print (1 :: Int)
