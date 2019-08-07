{-# OPTIONS --guardedness #-}

module ky where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Rational using (ℚ; _+_; _*_; _-_)
open import Data.Bool
open import Data.Bool.Properties
open import Data.Rational
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Empty
open import Relation.Nullary 
open import Relation.Nullary.Negation
open import Agda.Builtin.Size
open import Data.Product
open import Data.Unit

-- Cf. Abel 2017
record Cotree (i : Size) (A State : Set) : Set where
  coinductive
  field
    ν : Bool
    δ : ∀{j : Size< i} → A →  State → Cotree j A State
    upd : State → State    

open Cotree

∅ : ∀{A State : Set} {i : Size} → Cotree i A State
ν ∅     = false
δ ∅ _ _ = ∅
upd ∅ s = s

data Val : Set → Set where
  VBool : Bool → Val Bool
  VNat  : ℕ → Val ℕ

data Exp : Set → Set where
  EVal : ∀{t : Set} → Val t → Exp t

data Com : Set → Set₁ where
  CInc : Com ℕ
  CUpd : ∀{t : Set} → Exp t → Com t
  CIte : ∀{t : Set} → Exp Bool → Com t → Com t → Com t
  --CSeq : ∀{t : Set} → Com ⊤ → Com t → Com t
  --CWhile : ∀{t : Set} → Exp Bool → Com t → Com ⊤

State : Set
State = ℕ

eval : ∀{t : Set} → Exp t → State → t
eval (EVal (VBool b)) _ = b
eval (EVal (VNat n))  _ = n

interp : ∀{i : Size} → Com ℕ → Cotree i Bool State
interp CInc = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t     = true
        δ t _ _ = ∅
        upd t s = suc s
interp (CUpd e) = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t     = true
        δ t _ s = ∅
        upd t s = eval e s
interp (CIte e c₁ c₂) = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t = false
        δ t _ s = if eval e s then interp c₁ else interp c₂
        
{-interp (CSeq c₁ c₂) = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t = false
        δ t _ s = s , 
interp (CWhile e c) = t
  where t : ∀{j : Size} → Cotree j Bool State
        ν t = false
        δ t _ s = s , interp (CIte e -}




