open import Agda.Primitive hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

import Syntax

module Rank (Class : Set) where

  open Syntax Class

  rank : Shape → ℕ
  rank 𝟘 = 0
  rank [ γ , _ ] = suc (rank γ)
  rank (γ ++ δ) = (rank γ) ⊔ (rank δ)

  rank-< : ∀ {γ δ cl} (x : (γ , cl) ∈ δ) → rank γ < rank δ
  rank-< var-here = n<1+n _
  rank-< (var-left x) = m<n⇒m<n⊔o _ (rank-< x)
  rank-< (var-right y) = m<n⇒m<o⊔n _ (rank-< y)
