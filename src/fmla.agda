{-# OPTIONS --postfix-projections --safe --without-K #-}

module fmla (At : Set) where

data fmla : Set where
  `I : fmla
  +at -at : At → fmla
  `↑ `↓ : fmla → fmla
  _`⅋_ _`⊗_ _`&_ _`⊕_ _`▷_ : fmla → fmla → fmla

`¬ : fmla → fmla
`¬ `I = `I
`¬ (+at a) = -at a
`¬ (-at a) = +at a
`¬ (`↑ p) = `↓ (`¬ p)
`¬ (`↓ p) = `↑ (`¬ p)
`¬ (p `⅋ q) = `¬ p `⊗ `¬ q
`¬ (p `⊗ q) = `¬ p `⅋ `¬ q
`¬ (p `& q) = `¬ p `⊕ `¬ q
`¬ (p `⊕ q) = `¬ p `& `¬ q
`¬ (p `▷ q) = `¬ p `▷ `¬ q

mutual
  data pos : fmla → Set where
    `I : pos `I
    +at : (a : At) → pos (+at a)
    `↓ : ∀ {n} → neg n → pos (`↓ n)
    _`⊗_ : ∀ {p q} → pos p → pos q → pos (p `⊗ q)
    _`⊕_ : ∀ {p q} → pos p → pos q → pos (p `⊕ q)
    _`▷_ : ∀ {p q} → pos p → pos q → pos (p `▷ q)

  data neg : fmla → Set where
    `I : neg `I
    -at : (a : At) → neg (-at a)
    `↑ : ∀ {p} → pos p → neg (`↑ p)
    _`⅋_ : ∀ {n m} → neg n → neg m → neg (n `⅋ m)
    _`&_ : ∀ {n m} → neg n → neg m → neg (n `& m)
    _`▷_ : ∀ {n m} → neg n → neg m → neg (n `▷ m)
