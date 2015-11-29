{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

data Nat where
  S :: Nat -> Nat
  Z :: Nat

data PlusJudge :: Nat -> Nat -> Nat -> *  where
  PZero :: Nat -> PlusJudge Z n n
  PSucc :: Nat -> Nat -> Nat -> PlusJudge n1 n2 n3 -> PlusJudge (S n1) n2 (S n3)

data MultJudge :: Nat -> Nat -> Nat -> *  where
  TZero :: MultJudge Z n Z
  TSucc :: MultJudge n1 n2 n3 -> PlusJudge n2 n3 n4 -> MultJudge (S n1) n2 n4

eP5 :: PlusJudge (S (S Z)) (S (S (S (S Z)))) (S (S (S (S (S (S Z))))))
eP5 = PSucc (PSucc PZero)

foldPlusJudge :: (Nat -> a)
              -> (Nat -> Nat -> Nat -> PlusJudge n1 n2 n3 -> a -> a)
              -> Nat -> Nat -> Nat -> PlusJudge n4 n5 n6 -> a
foldPlusJudge =
-- foldPlusJudge f g (x@PZero)  = f x
-- foldPlusJudge f g (PSucc y)  = g y

{-
plusJudge_ind
     : forall P : nat -> nat -> nat -> Prop,
       (forall n : nat, P 0 n n) ->
       (forall n1 n2 n3 : nat,
        plusJudge n1 n2 n3 -> P n1 n2 n3 -> P (S n1) n2 (S n3)) ->
       forall n n0 n1 : nat, plusJudge n n0 n1 -> P n n0 n1
 -}

-- data Solve t = Solve ()

-- runPSucc :: Solve (PlusJudge (S n1) n2 (S n3)) -> Solve (PlusJudge n1 n2 n3)
-- runPSucc =


main = print 1
