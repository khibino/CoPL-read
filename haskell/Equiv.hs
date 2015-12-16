{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Equiv where

data a :=: b where
  Refl  :: a :=: a

eqSym :: a :=: b -> b :=: a
eqSym ab = case ab of
  Refl -> Refl

eqTrans :: a :=: b -> b :=: c -> a :=: c
eqTrans ab bc = case bc of
  Refl -> ab

eqCong :: a :=: b -> f a :=: f b
eqCong ab = case ab of
  Refl -> Refl
