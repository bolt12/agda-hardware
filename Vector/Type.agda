{-# OPTIONS --safe --without-K #-}

module Vector.Type {A : Set} where

open import Data.Unit using () renaming (⊤ to ⊤′)
open import Data.Product using () renaming (_×_ to _×′_)

open import Categorical.Raw

open import Data.Nat
open import Data.Vec

infixr 1 _⇨_

_⇨_ : ℕ → ℕ → Set
n ⇨ m = Vec A n → Vec A m

module ⇨-instances where

  instance

    products : Products ℕ
    products = record { ⊤ = zero ; _×_ = _+_ }
