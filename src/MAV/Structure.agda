{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.Structure (At : Set) where

open import MAV.Formula At

data Polarity : Set where
  + - : Polarity

private
  variable
    ± : Polarity

~_ : Polarity → Polarity
~ + = -
~ - = +

infixr 20 `_
infixr 15 `~_
infixr 10 _`⅋_
infixr 10 _`⊗_
infixr 10 _`&_
infixr 10 _`⊕_
infixr 10 _`▷_

data Structure : (± : Polarity) → Set where
  `I   : Structure    ± 
  `_   : Formula         → Structure ±
  `~_  : Structure (~ ±) → Structure ±
  _`⅋_ : Structure    -  → Structure - → Structure -
  _`⊗_ : Structure    +  → Structure + → Structure +
  _`&_ : Structure    -  → Structure - → Structure -
  _`⊕_ : Structure    +  → Structure + → Structure +
  _`▷_ : Structure    ±  → Structure ± → Structure ±
