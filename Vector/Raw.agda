{-# OPTIONS --safe --without-K #-}

open import Level

module Vector.Raw {A : Set} where

import Function as F
open import Data.Product as × using (_,_; proj₁; proj₂; <_,_>)
open import Data.Nat
open import Data.Vec

open import Categorical.Raw
open import Categorical.Equiv

open import Vector.Type {A} public

module ⇨-raw-instances where

  instance

    category : Category _⇨_
    category =
      record
        { id  = F.id
        ; _∘_ = F._∘′_
        }

    cartesian : Cartesian _⇨_ -- {Level.zero} ⦃ ⇨-instances.products ⦄ _⇨_
    cartesian =
      record
        { !   = λ _ → []
        ; _▵_ = λ a⇨c a⇨d a → a⇨c a ++ a⇨d a
        ; exl = take _
        ; exr = drop _
        }
