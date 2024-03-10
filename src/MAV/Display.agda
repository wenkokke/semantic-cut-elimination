{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Display (At : Set) where

open import MAV.Formula At
open import MAV.Structure At

private
  variable
    X X₁ X₂ : Structure +
    Y Y₁ Y₂ : Structure -

data _⊢_ :  Structure + → Structure - → Set where
  `axiom   : X ⊢ Y

  `mono-⅋  : X₁ ⊢ Y₁  →  X₂ ⊢ Y₂
             -------------------
           → X₁ `⅋ X₂ ⊢ Y₁ `⅋ Y₂

  `mono-⊗  : X₁ ⊢ Y₁  →  X₂ ⊢ Y₂
             -------------------
           → X₁ `⊗ X₂ ⊢ Y₁ `⊗ Y₂

  `mono-&₁ : X₁ ⊢ Y₁
             -------------------
           → X₁ `& X₂ ⊢ Y₁ `& Y₂

  `mono-&₂ : X₂ ⊢ Y₂
             -------------------
           → X₁ `& X₂ ⊢ Y₁ `& Y₂

  `mono-⊕₁ : X₁ ⊢ Y₁
             -------------------
           → X₁ `⊕ X₂ ⊢ Y₁ `⊕ Y₂

  `mono-⊕₂ : X₂ ⊢ Y₂
             -------------------
           → X₁ `⊕ X₂ ⊢ Y₁ `⊕ Y₂

  `mono-▷  : X₁ ⊢ Y₁   → X₂ ⊢ Y₂
             -------------------
           → X₁ `▷ X₂ ⊢ Y₁ `▷ Y₂
