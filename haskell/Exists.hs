{--# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{--# LANGUAGE KindSignatures #-}
{--# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{--# LANGUAGE ScopedTypeVariables #-}
{--# LANGUAGE FlexibleInstances #-}
{--# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{--# LANGUAGE AllowAmbiguousTypes #-}
{--# LANGUAGE FunctionalDependencies #-}

module Exists where


data Nat = Z
         | S Nat deriving (Eq,Ord,Show,Read)

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance (S m) :+ n = S (m :+ n)

type family (m :: Nat) :* (n :: Nat) :: Nat
type instance     Z :* n = Z
type instance (S m) :* n = (m :* n) :+ n

data Nat' (n :: Nat) where
  Z'    :: Nat' Z
  S'    :: Nat' n -> Nat' (S n)
  -- (:+:) :: Nat' m -> Nat' n -> Nat' (m :+ n)
  -- (:*:) :: Nat' m -> Nat' n -> Nat' (m :* n)

data Exists (k' :: k -> *) (p :: k -> *) where
  ExIntro :: k' a -> p a -> Exists k' p

data Plus (n1 :: Nat) (n2 :: Nat) (n3 :: Nat) where
  PZero :: Nat' n -> Plus Z n n
  PSucc :: Nat' n1 -> Nat' n2 -> Nat' n3 -> Plus n1 n2 n3 -> Plus (S n1) n2 (S n3)

plusExists :: Nat' n1 -> Nat' n2 -> Exists Nat' (Plus n1 n2)
plusExists Z'       n2 = ExIntro n2 (PZero n2)
plusExists (S' n1') n2 = case plusExists n1' n2 of
  ExIntro n3' p -> ExIntro (S' n3') (PSucc n1' n2 n3' p)


data NatExists (p :: Nat -> *)  where
  NatExIntro :: Nat' n -> p n -> NatExists p

-- plusExists' :: Nat' n1 -> Nat' n2 -> NatExists (Plus n1 n2)
-- plusExists' = undefined
