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
open import Relation.Nullary 
open import Relation.Nullary.Negation
open import Agda.Builtin.Size
open import Data.Product
open import Data.Unit
open import Data.Maybe

data QRE : Set → Set → Set₁ where
  ⊥ : ∀{D C} → QRE D C
  ε : ∀{D C} → C → QRE D C
  α : ∀{D C}
    → (D → Bool)  --φ
    → (D → C)     --op
    → QRE D C
  split : ∀{D C B A}
    → QRE D A     --f
    → QRE D B     --g
    → (A → B → C) --op
    → QRE D C
  iter : ∀{D B A}
    → QRE D B     --init
    → QRE D A     --body 
    → (B → A → B) --op
    → QRE D B
  or : ∀{D C}
    → QRE D C
    → QRE D C
    → QRE D C

Event : Set
Event = ℕ

data Val : Set → Set where
  VBool : Bool → Val Bool
  VNat  : ℕ → Val ℕ

data Exp : Set → Set where
  EVal : ∀{t : Set} → Val t → Exp t

data Com : Set → Set where
  CFlip : ∀{t} → Com t → Com t → Com t
  CUpd  : Exp Event → Com ⊤
  CIte  : ∀{t} → Exp Bool → Com t → Com t → Com t
  CSeq  : ∀{t} → Com ⊤ → Com t → Com t

is-true : Bool → Bool
is-true = λ{x → x}

data CoList (i : Size) (A : Set) : Set where
  nil  : CoList i A
  cons : A → ∀{j : Size< i} → CoList j A → CoList i A 
      
_++_ : ∀{A} → CoList ∞ A → CoList ∞ A → CoList ∞ A
nil         ++ s₂ = s₂
(cons a s₁) ++ s₂ = cons a (s₁ ++ s₂)

interp : Com ⊤ → QRE Bool (CoList ∞ Event)
interp (CFlip c₁ c₂) =
  or (split (α is-true λ{_ → nil}) (interp c₁) (_++_))
     (split (α not     λ{_ → nil}) (interp c₂) (_++_))



