{-# OPTIONS --postfix-projections --safe --without-K #-}

module fmlactx (At : Set) where

open import fmla At renaming (`¬ to fmla-`¬)

data fmlactx : Set where
  `□ : fmlactx
  _〈`⅋_ : fmlactx → fmla → fmlactx
  _`⅋〉_ : fmla → fmlactx → fmlactx
  _〈`⊗_ : fmlactx → fmla → fmlactx
  _`⊗〉_ : fmla → fmlactx → fmlactx
  _〈`&_ : fmlactx → fmla → fmlactx
  _`&〉_ : fmla → fmlactx → fmlactx
  _〈`⊕_ : fmlactx → fmla → fmlactx
  _`⊕〉_ : fmla → fmlactx → fmlactx
  _〈`▷_ : fmlactx → fmla → fmlactx
  _`▷〉_ : fmla → fmlactx → fmlactx

_[_] : fmlactx → fmla → fmla
`□ [ p ] = p
(ξ 〈`⅋ x) [ p ] = (ξ [ p ]) `⅋ x
(x `⅋〉 ξ) [ p ] = x `⅋ (ξ [ p ])
(ξ 〈`⊗ x) [ p ] = (ξ [ p ]) `⊗ x
(x `⊗〉 ξ) [ p ] = x `⊗ (ξ [ p ])
(ξ 〈`& x) [ p ] = (ξ [ p ]) `& x
(x `&〉 ξ) [ p ] = x `& (ξ [ p ])
(ξ 〈`⊕ x) [ p ] = (ξ [ p ]) `⊕ x
(x `⊕〉 ξ) [ p ] = x `⊕ (ξ [ p ])
(ξ 〈`▷ x) [ p ] = (ξ [ p ]) `▷ x
(x `▷〉 ξ) [ p ] = x `▷ (ξ [ p ])

`¬ : fmlactx → fmlactx
`¬ `□ = `□ 
`¬ (ξ 〈`⅋ q) = `¬ ξ 〈`⊗ fmla-`¬ q
`¬ (p `⅋〉 ξ) = fmla-`¬ p `⊗〉 `¬ ξ
`¬ (ξ 〈`⊗ q) = `¬ ξ 〈`⅋ fmla-`¬ q
`¬ (p `⊗〉 ξ) = fmla-`¬ p `⅋〉 `¬ ξ
`¬ (ξ 〈`& q) = `¬ ξ 〈`⊕ fmla-`¬ q
`¬ (p `&〉 ξ) = fmla-`¬ p `⊕〉 `¬ ξ
`¬ (ξ 〈`⊕ q) = `¬ ξ 〈`& fmla-`¬ q
`¬ (p `⊕〉 ξ) = fmla-`¬ p `&〉 `¬ ξ
`¬ (ξ 〈`▷ q) = `¬ ξ 〈`▷ fmla-`¬ q
`¬ (p `▷〉 ξ) = fmla-`¬ p `▷〉 `¬ ξ
 