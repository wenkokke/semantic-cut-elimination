{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Structure (At : Set) where

data Polarity : Set where
  + - : Polarity

private
  variable
    ± : Polarity

¬ : Polarity → Polarity
¬ + = -
¬ - = +

data Structure : (± : Polarity) → Set where
  `I   : Structure    ±
  `_   : Structure    ±
  `¬_  : Structure (¬ ±) → Structure ±
  _`⅋_ : Structure    -  → Structure - → Structure -
  _`⊗_ : Structure    +  → Structure + → Structure +
  _`&_ : Structure    -  → Structure - → Structure -
  _`⊕_ : Structure    +  → Structure + → Structure +
  _`▷_ : Structure    ±  → Structure ± → Structure ±
