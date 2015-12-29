{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}

module Nat where

import Peano
import Equiv


data Plus (n1 :: Nat) (n2 :: Nat) (n3 :: Nat) where
  PZero :: Nat' n -> Plus 'Z n n
  PSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus ('S n1) n2 ('S n3)

eqZeroPlus :: Nat' n -> Nat' n' -> Plus 'Z n n' -> n :=: n'
eqZeroPlus _ _ (PZero _) = Refl

plusUnique :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Nat' n4
           -> Plus n1 n2 n3 -> Plus n1 n2 n4
           -> n3 :=: n4
plusUnique  Z'     n2  n3     n4      j@(PZero {})    k@(PZero {})
  = eqTrans (eqSym (eqZeroPlus n2 n3 j)) (eqZeroPlus n2 n4 k)
plusUnique  Z'     _   _      _       (PZero {})      k {-PSucc-}
  = case k of {}
plusUnique  Z'     _   _      _       j {-PSucc-}     _
  = case j of {}
plusUnique (S' _)  _   Z'     _       j               _
  = case j of {}
plusUnique (S' _)  _  (S' _)  Z'      _               k
  = case k of {}
plusUnique (S' n1) n2 (S' n3) (S' n4) (PSucc _ _ _ j) (PSucc _ _ _ j')
  = eqCong (plusUnique n1 n2 n3 n4 j j')
plusUnique (S' _)  _  (S' _)  (S' _)  (PSucc  {})      k  {-PZero-}
  = case k of {}
plusUnique (S' _)  _  (S' _)  (S' _)  j {-PZero-}      _
  = case j of {}
