{-# OPTIONS --postfix-projections --safe --without-K #-}

module fmla (At : Set) where

data fmla : Set where
  `I : fmla
  +at -at : At → fmla
  _`⅋_ _`⊗_ _`&_ _`⊕_ _`▷_ : fmla → fmla → fmla

`¬ : fmla → fmla
`¬ `I = `I
`¬ (+at a) = -at a
`¬ (-at a) = +at a
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q

infixr 30 `↓_
infixr 30 `↑_
infixl 25 _`⊗_
infixl 25 _`⊝_
infixl 25 _`⅋_
infixl 25 _`▷_
infixl 25 _`⊕_
infixl 25 _`&_

data pol : Set where
  + - : pol

data fml : pol → Set where
  `I : ∀ {ρ} → fml ρ
  +at : At → fml +
  -at : At → fml -
  `↓_ : fml - → fml +
  `↑_ : fml + → fml -
  _`⊗_ _`⊕_ : fml + → fml + → fml +
  _`⊝_ : fml + → fml - → fml +
  _`⅋_ _`&_ : fml - → fml - → fml -
  _`▷_ : ∀ {ρ} → fml ρ → fml ρ → fml ρ

data rct : fml - → Set where
  -at : (a : At) → rct (-at a)
  `↑_ : (p : fml +) → rct (`↑ p)
