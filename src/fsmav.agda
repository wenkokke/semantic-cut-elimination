{-# OPTIONS --postfix-projections --safe --without-K #-}

module fsmav (At : Set) where

open import Level
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)
open import basics

open import fmla At

data _⟶_ : fmla → fmla → Set where
  `axiom    : ∀ p → (p `⅋ `¬ p) ⟶ `I
  `cut      : ∀ p → `I ⟶ (p `⊗ `¬ p)

  `tidy     : (`I `& `I) ⟶ `I
  `switch   : ∀ {p q r} → ((p `⊗ q) `⅋ r) ⟶ (p `⊗ (q `⅋ r))
  `sequence : ∀ {p q r s} → ((p `▷ q) `⅋ (r `▷ s)) ⟶ ((p `⅋ r) `▷ (q `⅋ s))
  `left     : ∀ {p q} → (p `⊕ q) ⟶ p
  `right    : ∀ {p q} → (p `⊕ q) ⟶ q
  `external : ∀ {p q r} → ((p `& q) `⅋ r) ⟶ ((p `⅋ r) `& (q `⅋ r))
  `medial   : ∀ {p q r s} → ((p `▷ q) `& (r `▷ s)) ⟶ ((p `& r) `▷ (q `& s))

  _⟨`⊗_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p `⊗ q) ⟶ (p' `⊗ q)
  _`⊗⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p `⊗ q) ⟶ (p `⊗ q')
  `⊗-assoc   : ∀ {p q r} → (p `⊗ (q `⊗ r)) ⟶ ((p `⊗ q) `⊗ r)
  `⊗-assoc⁻¹ : ∀ {p q r} → ((p `⊗ q) `⊗ r) ⟶ (p `⊗ (q `⊗ r))
  `⊗-comm    : ∀ {p q} → (p `⊗ q) ⟶ (q `⊗ p)
  `⊗-unit    : ∀ {p}   → (p `⊗ `I) ⟶ p
  `⊗-unit⁻¹  : ∀ {p}   → p ⟶ (p `⊗ `I)

  _⟨`⅋_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p `⅋ q) ⟶ (p' `⅋ q)
  _`⅋⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p `⅋ q) ⟶ (p `⅋ q')
  `⅋-assoc   : ∀ {p q r} → (p `⅋ (q `⅋ r)) ⟶ ((p `⅋ q) `⅋ r)
  `⅋-assoc⁻¹ : ∀ {p q r} → ((p `⅋ q) `⅋ r) ⟶ (p `⅋ (q `⅋ r))
  `⅋-comm    : ∀ {p q} → (p `⅋ q) ⟶ (q `⅋ p)
  `⅋-unit    : ∀ {p}   → (p `⅋ `I) ⟶ p
  `⅋-unit⁻¹  : ∀ {p}   → p ⟶ (p `⅋ `I)

  _⟨`▷_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p `▷ q) ⟶ (p' `▷ q)
  _`▷⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p `▷ q) ⟶ (p `▷ q')
  `▷-assoc   : ∀ {p q r} → (p `▷ (q `▷ r)) ⟶ ((p `▷ q) `▷ r)
  `▷-assoc⁻¹ : ∀ {p q r} → ((p `▷ q) `▷ r) ⟶ (p `▷ (q `▷ r))
  `▷-runit   : ∀ {p}   → (p `▷ `I) ⟶ p
  `▷-runit⁻¹ : ∀ {p}   → p ⟶ (p `▷ `I)
  `▷-lunit   : ∀ {p}   → (`I `▷ p) ⟶ p
  `▷-lunit⁻¹ : ∀ {p}   → p ⟶ (`I `▷ p)

  _⟨`&_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p `& q) ⟶ (p' `& q)
  _`&⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p `& q) ⟶ (p `& q')

  _⟨`⊕_      : ∀ {p p'} → p ⟶ p' → (q : fmla) → (p `⊕ q) ⟶ (p' `⊕ q)
  _`⊕⟩_      : ∀ {q q'} → (p : fmla) → q ⟶ q' → (p `⊕ q) ⟶ (p `⊕ q')