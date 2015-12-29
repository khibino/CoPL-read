{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Peano where


data Nat = Z
         | S Nat deriving (Eq,Ord,Show,Read)

-- type family (m :: Nat) :+ (n :: Nat) :: Nat
-- type instance 'Z :+ n = n
-- type instance ('S m) :+ n = 'S (m :+ n)

-- type family (m :: Nat) :* (n :: Nat) :: Nat
-- type instance     'Z :* n = 'Z
-- type instance ('S m) :* n = (m :* n) :+ n

data Nat' (n :: Nat) where
  Z'    :: Nat' 'Z
  S'    :: Nat' n -> Nat' ('S n)
