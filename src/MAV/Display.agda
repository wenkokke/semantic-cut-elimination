{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Display (At : Set) where

open import MAV.Formula At
open import MAV.Structure At

private
  variable
    A A′ A₁ A₂ A₃ : Formula 
    B B′ B₁ B₂ B₃ : Formula
    X X′ X₁ X₂ X₃ : Structure +
    Y Y′ Y₁ Y₂ Y₃ : Structure -

infix 5 _⊢_

data _⊢_ :  Structure + → Structure - → Set where


  `axiom      : X ⊢ Y

  `mono-⅋     : ` A₁ ⊢ Y₁
              → ` A₂ ⊢ Y₂
                ------------------------
              → `( A₁ `⅋ A₂ ) ⊢ Y₁ `⅋ Y₂

  `rewr-⅋     : X ⊢ ` B₁ `⅋ ` B₂
                -----------------
              → X ⊢ `( B₁ `⅋ B₂ )

  `comm-⅋     : X ⊢ Y₁ `⅋ Y₂
                ------------
              → X ⊢ Y₂ `⅋ Y₁

  `assoc-⅋    : X ⊢ Y₁ `⅋ (Y₂ `⅋ Y₃)
                --------------------
              → X ⊢ (Y₁ `⅋ Y₂) `⅋ Y₃

  `assoc-⅋⁻¹  : X ⊢ (Y₁ `⅋ Y₂) `⅋ Y₃
                --------------------
              → X ⊢ Y₁ `⅋ (Y₂ `⅋ Y₃)

  `mono-⊗     : X₁ ⊢ ` B₁
              → X₂ ⊢ ` B₂
                ------------------------
              → X₁ `⊗ X₂ ⊢ `( B₁ `⊗ B₂ )

  `rewr-⊗     : ` A₁ `⊗ ` A₂ ⊢ Y
                -----------------
              → `( A₁ `⊗ A₂ ) ⊢ Y

  `res-⊗₁     : X₁ `⊗ X₂ ⊢ Y
                ---------------
              → X₂ ⊢ `~ X₁ `⅋ Y

  `res-⊗₁⁻¹   : X₂ ⊢ `~ X₁ `⅋ Y
                ---------------
              → X₁ `⊗ X₂ ⊢ Y

  `res-⊗₂     : X₁ `⊗ X₂ ⊢ Y
                ---------------
              → X₁ ⊢ Y `⅋ `~ X₂

  `res-⊗₂⁻¹   : X₁ ⊢ Y `⅋ `~ X₂
                ---------------
              → X₁ `⊗ X₂ ⊢ Y

  `comm-⊗     : X₁ `⊗ X₂ ⊢ Y
                ------------
              → X₂ `⊗ X₁ ⊢ Y

  `assoc-⊗    : X₁ `⊗ (X₂ `⊗ X₃) ⊢ Y
                --------------------
              → (X₁ `⊗ X₂) `⊗ X₃ ⊢ Y

  `assoc-⊗⁻¹  : (X₁ `⊗ X₂) `⊗ X₃ ⊢ Y
                --------------------
              → X₁ `⊗ (X₂ `⊗ X₃) ⊢ Y

  `mono-▷ᴸ    : ` A₁ ⊢ Y₁
              → ` A₂ ⊢ Y₂
                ------------------------
              → `( A₁ `▷ A₂ ) ⊢ Y₁ `▷ Y₂

  `rewr-▷ᴸ    : ` A₁ `▷ ` A₂ ⊢ Y
                -----------------
              → `( A₁ `▷ A₂ ) ⊢ Y

  `res-▷₁ᴸ    : X₁ `▷ X₂ ⊢ Y
                ---------------
              → X₂ ⊢ `~ X₁ `▷ Y

  `res-▷₁ᴸ⁻¹  : X₂ ⊢ `~ X₁ `▷ Y
                ---------------
              → X₁ `▷ X₂ ⊢ Y

  `res-▷₂ᴸ    : X₁ `▷ X₂ ⊢ Y
                ---------------
              → X₁ ⊢ Y `▷ `~ X₂

  `res-▷₂ᴸ⁻¹  : X₁ ⊢ Y `▷ `~ X₂
                ---------------
              → X₁ `▷ X₂ ⊢ Y

  `assoc-▷ᴸ   : X₁ `▷ (X₂ `▷ X₃) ⊢ Y
                --------------------
              → (X₁ `▷ X₂) `▷ X₃ ⊢ Y

  `assoc-▷ᴸ⁻¹ : (X₁ `▷ X₂) `▷ X₃ ⊢ Y
                --------------------
              → X₁ `▷ (X₂ `▷ X₃) ⊢ Y

  `mono-▷ᴿ    : X₁ ⊢ ` B₁
              → X₂ ⊢ ` B₂
                ------------------------
              → X₁ `▷ X₂ ⊢ `( B₁ `▷ B₂ )

  `rewr-▷ᴿ    : X ⊢ ` B₁ `▷ ` B₂
                -----------------
              → X ⊢ `( B₁ `▷ B₂ )

  `res-▷₁ᴿ    : X ⊢ Y₁ `▷ Y₂
                ---------------
              → `~ Y₁ `▷ X ⊢ Y₂

  `res-▷₁ᴿ⁻¹  : `~ Y₁ `▷ X ⊢ Y₂
                ---------------
              → X ⊢ Y₁ `▷ Y₂

  `res-▷₂ᴿ    : X ⊢ Y₁ `▷ Y₂
                ---------------
              → X `▷ `~ Y₂ ⊢ Y₁

  `res-▷₂ᴿ⁻¹  : X `▷ `~ Y₂ ⊢ Y₁
                ---------------
              → X ⊢ Y₁ `▷ Y₂

  `assoc-▷ᴿ   : X ⊢ Y₁ `▷ (Y₂ `▷ Y₃)
                --------------------
              → X ⊢ (Y₁ `▷ Y₂) `▷ Y₃

  `assoc-▷ᴿ⁻¹ : X ⊢ (Y₁ `▷ Y₂) `▷ Y₃
                --------------------
              → X ⊢ Y₁ `▷ (Y₂ `▷ Y₃)

  `mono-&₁    : (A₂ : Formula)
              → (Y₂ : Structure -)
              → ` A₁ ⊢ Y₁
                ------------------------
              → `( A₁ `& A₂ ) ⊢ Y₁ `& Y₂

  `mono-&₂    : (A₁ : Formula)
              → (Y₁ : Structure -)
              → ` A₂ ⊢ Y₂
                ------------------------
              → `( A₁ `& A₂ ) ⊢ Y₁ `& Y₂

  `rewr-&     : X ⊢ ` B₁ `& ` B₂
                -----------------
              → X ⊢ `( B₁ `& B₂ )

  `mono-⊕₁    : (X₂ : Structure +)
              → (B₂ : Formula)
              → X₁ ⊢ ` B₁
                ------------------------
              → X₁ `⊕ X₂ ⊢ `( B₁ `⊕ B₂ )

  `mono-⊕₂    : (X₁ : Structure +)
              → (B₁ : Formula)
              → X₂ ⊢ ` B₂
                ------------------------
              → X₁ `⊕ X₂ ⊢ `( B₁ `⊕ B₂ )

  `rewr-⊕     : ` A₁ `⊕ ` A₂ ⊢ Y
                -----------------
              → `( A₁ `⊕ A₂ ) ⊢ Y
