{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Peano where


data Nat = Z
         | S Nat deriving (Eq,Ord,Show,Read)

data Nat' (n :: Nat) where
  Z'    :: Nat' 'Z
  S'    :: Nat' n -> Nat' ('S n)
