{-# OPTIONS --safe --without-K #-}

-- A linearizing category, parametrized by routings and primitives. This
-- category embodies a normal form for monoidal formulas as a strictly linear
-- composition of form:
--
--     rₙ ∘ first pₙ₋₁ ∘ rₙ₋₁ ⋯ ∘ first p₀ ∘ r₀
--  
-- where the `pᵢ` are primitive operations and the `rᵢ` are pure routings. This
-- category was designed to capture the simple essence of stack machines and
-- compiling to them homomorphically. It appears also to capture SSA and
-- hardware netlists nicely. Primitives always operate on the first part of a
-- pair ("the accumulator") while preserving the second ("the stack").
-- See http://conal.net/papers/calculating-compilers-categorically .

open import Categorical.Raw

module Linearize.Type
         {o}{objₘ : Set o} {ℓₘ}(_⇨ₘ_ : objₘ → objₘ → Set ℓₘ)
         {ℓ}{obj : Set ℓ} ⦃ _ : Products obj ⦄ ⦃ _ : Exponentials obj ⦄
         (_⇨ₚ_ : obj → obj → Set ℓ) (let infix 0 _⇨ₚ_; _⇨ₚ_ = _⇨ₚ_)
         (_⇨ᵣ_ : obj → obj → Set ℓ) (let infix 0 _⇨ᵣ_; _⇨ᵣ_ = _⇨ᵣ_)
  where

private variable a b c d z : obj

mutual

  infix 0 _⇨_
  infixr 9 _∘·first_∘_
  data _⇨_ : obj → obj → Set ℓ where
    ⌞_⌟ : (r : a ⇨ᵣ b) → (a ⇨ b)
    _∘·first_∘_ : (f : c × z ⇨ d) (p : b ⇨ᵤ c) (r : a ⇨ᵣ b × z) → (a ⇨ d)

  infix 0 _⇨ᵤ_
  data _⇨ᵤ_ : obj → obj → Set ℓ where
    `prim  : (a ⇨ₚ b) → (a ⇨ᵤ b)
    `apply : (a ⇛ b) × a ⇨ᵤ b
    `curry : (a × b ⇨ c) → (a ⇨ᵤ (b ⇛ c))

  -- TODO: Consider uncurry in place of apply
