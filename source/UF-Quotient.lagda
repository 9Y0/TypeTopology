Martin Escardo, August 2018.

Set quotients in univalent mathematics in Agda notation.

This took place during the Dagstuhl meeting "Formalization of
Mathematics in Type Theory", because Dan Grayson wanted to see how
universe levels work in Agda and I thought that this would be a nice
example to illustrate that.

We assume, in addition to Spartan Martin-Löf type theory,

 * function extensionality
   (any two pointwise equal functions are equal),

 * propositional extensionality
   (any two logically equivalent propositions are equal),

 * propositional truncation
   (any type can be universally mapped into a prop in the same
   universe),

and no resizing axioms.

The K axiom is not used (the without-K option below). We also make
sure pattern matching corresponds to Martin-Löf eliminators, using the
option exact-split. With the option safe we make sure that nothing
is postulated - any non-MLTT axiom has to be an explicit assumption
(argument to a function or a module).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection
open import UF-Equiv

module UF-Quotient
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

\end{code}

We define when a relation is subsingleton (or proposition) valued,
reflexive, transitive or an equivalence.

What is noteworthy, for the purpose of explaining universes in Agda to
Dan, is that X is in a universe 𝓤, and the value of the relation is in
a universe 𝓥, where 𝓤 and 𝓥 are arbitrary.

(NB. The Agda library uses the word "Level" for universes, and then
what we write "𝓤 ̇" here is written "Set 𝓤". This is not good for
univalent mathematics, because the types in 𝓤 ̇ need not be sets, and
also because it places emphasis on levels rather than universes
themselves.)

Then, for example, the function is-prop-valued defined below takes
values in the least upper bound of 𝓤 and 𝓥, which is denoted by 𝓤 ⊔ 𝓥.

We first define the type of five functions and then define them, where
_≈_ is a variable:

\begin{code}

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

\end{code}

Now, using an anonymous module with parameters (corresponding to a
section in Coq), we assume propositional truncations that stay in the
same universe, function extensionality for all universes, two
universes 𝓤 and 𝓥, propositional truncation for the universe 𝓥, a type
X : 𝓤 ̇, and an equivalence relation _≈_ with values in 𝓥 ̇.

\begin{code}

module quotient
       {𝓤 𝓥 : Universe}
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-prop-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

\end{code}

Now, Ω 𝓥 is the type of subsingletons, or (univalent) propositions, or
h-propositions, or mere propositions, in the universe 𝓥, which lives
in the next universe 𝓥 ⁺.

From the relation _≈_ : X → (X → 𝓥 ̇ ) we define a relation
X → (X → Ω 𝓥), which of course is formally a function. We then take
the quotient X/≈ to be the image of this function.

Of course, it is for constructing the image that we need propositional
truncations.

\begin{code}

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = x ≈ y , ≈p x y

\end{code}

Then the quotient lives in the least upper bound of 𝓤 and 𝓥 ⁺, where 𝓥 ⁺
is the successor of the universe 𝓥:

\begin{code}

 X/≈ : 𝓤 ⊔ (𝓥 ⁺) ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
                (powersets-are-sets'' fe fe pe)
                ∥∥-is-prop

 η : X → X/≈
 η = corestriction equiv-rel

\end{code}

Then η is the universal solution to the problem of transforming
equivalence _≈_ into equality _≡_ (in Agda the notation for the
identity type is _≡_ - we can't use _=_ because this is a reserved
symbol for definitional equality).

By construction, η is a surjection, of course:

\begin{code}

 η-surjection : is-surjection η
 η-surjection = corestriction-is-surjection equiv-rel

\end{code}

It is convenient to use the following induction principle for
reasoning about the image. Notice that the property we consider has
values in any universe 𝓦 we please:

\begin{code}

 quotient-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
                    → ((x' : X/≈) → is-prop (P x'))
                    → ((x : X) → P (η x))
                    → (x' : X/≈) → P x'
 quotient-induction = surjection-induction η η-surjection

\end{code}

The first part of the universal property of η says that equivalent
points are mapped to equal points:

\begin{code}

 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e =
   to-Σ-≡ (dfunext fe
          (λ z → to-Σ-≡ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                         being-prop-is-prop fe _ _)) ,
       ∥∥-is-prop _ _)

\end{code}

We also need the fact that η reflects equality into equivalence:

\begin{code}

 η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ≡ (x ≈ y)
     a = ap (λ - → pr₁ (- y)) (q ⁻¹)
     b : (y ≈ y) → (x ≈ y)
     b = Idtofun a

\end{code}

We are now ready to formulate and prove the universal property of the
quotient. What is noteworthy here, regarding universes, is that the
universal property says that we can eliminate into any set A of any
universe 𝓦.

                   η
              X ------> X/≈
               \       .
                \     .
               f \   . f'
                  \ .
                   v
                   A

\begin{code}

 universal-property : ∀ {𝓦} (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ≡ f x')
                    → ∃! f' ꞉ ( X/≈ → A), f' ∘ η ≡ f
 universal-property {𝓦} A iss f pr = ic
  where
   φ : (x' : X/≈) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ x') × (f x ≡ a))
   φ = quotient-induction _ γ induction-step
     where
      induction-step : (y : X) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ η y) × (f x ≡ a))
      induction-step x (a , d) (b , e) = to-Σ-≡ (p , ∥∥-is-prop _ _)
       where
        h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a))
          → (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b))
          → a ≡ b
        h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ pr (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

        p : a ≡ b
        p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

      γ : (x' : X/≈) → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)))
      γ x' = being-prop-is-prop fe

   k : (x' : X/≈) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)
   k = quotient-induction _ φ induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ≡ f
   r = dfunext fe h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))) → f' (η y) ≡ f y
     j y (x , p , q) = q ⁻¹ ∙ pr (η-equal-equiv p)

     h : (y : X) → f' (η y) ≡ f y
     h y = ∥∥-rec iss (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-≡ (t , v)
    where
     w : ∀ x → f' (η x) ≡ f'' (η x)
     w = happly (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = dfunext fe (quotient-induction _ (λ _ → iss) w)

     u : f'' ∘ η ≡ f
     u = transport (λ - → - ∘ η ≡ f) t r

     v : u ≡ s
     v = Π-is-set fe (λ _ → iss) u s

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ≡ f
   ic = (f' , r) , c

\end{code}

Added 11th February 2021. We now repackage the above for convenient
use:

\begin{code}

module _ {𝓤 𝓥 : Universe} where

 open quotient
 open ImageAndSurjection pt

 EqRel : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 EqRel X = Σ R ꞉ (X → X → 𝓥 ̇ ) , is-equiv-relation R

 _≈[_]_ : {X : 𝓤 ̇ } → X → EqRel X → X → 𝓥 ̇
 x ≈[ _≈_ , _ ] y = x ≈ y

 _/_ : (X : 𝓤 ̇ ) → EqRel X → 𝓤 ⊔ (𝓥 ⁺) ̇
 X / (_≈_ , p , r , s , t) = X/≈ X _≈_ p r s t

 module _ {X : 𝓤 ̇ }
          ((_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel X)
        where

  private
   ≋ : EqRel X
   ≋ = (_≈_ , ≈p , ≈r , ≈s , ≈t)

  quotient-is-set : is-set (X / ≋)
  quotient-is-set = X/≈-is-set _ _≈_ ≈p ≈r ≈s ≈t

  η/ : X → X / ≋
  η/ = η X _≈_ ≈p ≈r ≈s ≈t

  η/-is-surjection : is-surjection η/
  η/-is-surjection = η-surjection X _≈_ ≈p ≈r ≈s ≈t

  /-induction : ∀ {𝓦} (P : X / ≋ → 𝓦 ̇ )
              → ((x' : X / ≋) → is-prop (P x'))
              → ((x : X) → P (η/ x))
              → (x' : X / ≋) → P x'
  /-induction = surjection-induction η/ η/-is-surjection

  /-induction' : ∀ {𝓦} {P : X / ≋ → 𝓦 ̇ }
               → ((x' : X / ≋) → is-prop (P x'))
               → ((x : X) → P (η/ x))
               → (x' : X / ≋) → P x'
  /-induction' {𝓦} {P} = surjection-induction η/ η/-is-surjection P

  identifies-related-points : {A : 𝓦 ̇ } → (X → A) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  identifies-related-points f = ∀ {x x'} → x ≈ x' → f x ≡ f x'

  η/-identifies-related-points : identifies-related-points η/
  η/-identifies-related-points = η-equiv-equal X _≈_ ≈p ≈r ≈s ≈t

  η/-relates-identified-points : {x y : X}
                               → η/ x ≡ η/ y
                               → x ≈ y
  η/-relates-identified-points = η-equal-equiv X _≈_ ≈p ≈r ≈s ≈t

  module _ {𝓦 : Universe}
           {A : 𝓦 ̇ }
         where

   abstract
    universal-property/ : is-set A
                        → (f : X → A)
                        → identifies-related-points f
                        → ∃! f' ꞉ (X / ≋ → A), f' ∘ η/ ≡ f
    universal-property/ = universal-property X _≈_ ≈p ≈r ≈s ≈t A

    mediating-map/ : is-set A
                   → (f : X → A)
                   → identifies-related-points f
                   → X / ≋ → A
    mediating-map/ i f p = pr₁ (center (universal-property/ i f p))

    universality-triangle/≡ : (i : is-set A) (f : X → A)
                              (p : identifies-related-points f)
                            → mediating-map/ i f p ∘ η/ ≡ f
    universality-triangle/≡ i f p = pr₂ (center (universal-property/ i f p))


    universality-triangle/ : (i : is-set A) (f : X → A)
                             (p : identifies-related-points f)
                           → mediating-map/ i f p ∘ η/ ∼ f
    universality-triangle/ i f p = happly (universality-triangle/≡ i f p)


    at-most-one-mediating-map/≡ : is-set A
                               → (g h : X / ≋ → A)
                               → g ∘ η/ ≡ h ∘ η/
                               → g ≡ h
    at-most-one-mediating-map/≡ i g h p = q ⁻¹ ∙ r
     where
      f : X → A
      f = g ∘ η/

      j : identifies-related-points f
      j e = ap g (η/-identifies-related-points e)

      q : mediating-map/ i f j ≡ g
      q = witness-uniqueness (λ f' → f' ∘ η/ ≡ f)
           (universal-property/ i f j)
           (mediating-map/ i f j) g (universality-triangle/≡ i f j)
           refl

      r : mediating-map/ i f j ≡ h
      r = witness-uniqueness (λ f' → f' ∘ η/ ≡ f)
           (universal-property/ i f j)
           (mediating-map/ i f j) h (universality-triangle/≡ i f j)
           (p ⁻¹)

    at-most-one-mediating-map/ : is-set A
                               → (g h : X / ≋ → A)
                               → g ∘ η/ ∼ h ∘ η/
                               → g ∼ h
    at-most-one-mediating-map/ i g h p = happly (at-most-one-mediating-map/≡ i g h
                                                   (dfunext fe p))
\end{code}

Extending unary and binary operations to the quotient:

\begin{code}

  extension/ : (f : X → X / ≋)
             → identifies-related-points f
             → (X / ≋ → X / ≋)
  extension/ = mediating-map/ quotient-is-set

  extension-triangle/ : (f : X → X / ≋)
                        (i : identifies-related-points f)
                      → extension/ f i ∘ η/ ∼ f
  extension-triangle/ = universality-triangle/ quotient-is-set

  module _ (f : X → X)
           (p : {x y : X} → x ≈ y → f x ≈ f y)
         where

   abstract
    private
      π : identifies-related-points (η/ ∘ f)
      π e = η/-identifies-related-points (p e)

   extension₁/ : X / ≋ → X / ≋
   extension₁/ = extension/ (η/ ∘ f) π

   naturality/ : extension₁/ ∘ η/ ∼ η/ ∘ f
   naturality/ = universality-triangle/ quotient-is-set (η/ ∘ f) π

  module _ (f : X → X → X)
           (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → f x y ≈ f x' y')
         where

   abstract
    private
     π : (x : X) → identifies-related-points (η/ ∘ f x)
     π x {y} {y'} e = η/-identifies-related-points (p {x} {y} {x} {y'} (≈r x) e)

     p' : (x : X) {y y' : X} → y ≈ y' → f x y ≈ f x y'
     p' x {x'} {y'} = p {x} {x'} {x} {y'} (≈r x)

     f₁ : X → X / ≋ → X / ≋
     f₁ x = extension₁/ (f x) (p' x)

     n/ : (x : X) → f₁ x ∘ η/ ∼ η/ ∘ f x
     n/ x = naturality/ (f x) (p' x)

     δ : {x x' : X} → x ≈ x' → (y : X) → f₁ x (η/ y) ≡ f₁ x' (η/ y)
     δ {x} {x'} e y =
       f₁ x (η/ y)   ≡⟨ naturality/ (f x) (p' x) y ⟩
       η/ (f x y)    ≡⟨ η/-identifies-related-points (p e (≈r y)) ⟩
       η/ (f x' y)   ≡⟨ (naturality/ (f x') (p' x') y)⁻¹ ⟩
       f₁ x' (η/ y)  ∎

     ρ : (b : X / ≋) {x x' : X} → x ≈ x' → f₁ x b ≡ f₁ x' b
     ρ b {x} {x'} e = /-induction (λ b → f₁ x b ≡ f₁ x' b)
                        (λ y → quotient-is-set) (δ e) b

     f₂ : X / ≋ → X / ≋ → X / ≋
     f₂ d e = extension/ (λ x → f₁ x e) (ρ e) d

   extension₂/ : X / ≋ → X / ≋ → X / ≋
   extension₂/ = f₂

   abstract
    naturality₂/ : (x y : X) → f₂ (η/ x) (η/ y) ≡ η/ (f x y)
    naturality₂/ x y =
     f₂ (η/ x) (η/ y) ≡⟨ extension-triangle/ (λ x → f₁ x (η/ y)) (ρ (η/ y)) x ⟩
     f₁ x (η/ y)      ≡⟨ naturality/ (f x) (p (≈r x)) y ⟩
     η/ (f x y)       ∎

\end{code}

Without the above abstract declarations, the use of naturality₂/ takes
for ever in the module FreeGroup.lagda.


Added in March 2022 by Tom de Jong.
We extend unary and binary prop-valued relations to the quotient.

\begin{code}

  module _ (r : X → Ω 𝓣)
           (p : {x y : X} → x ≈ y → r x ≡ r y)
         where

   extension-rel₁ : X / ≋ → Ω 𝓣
   extension-rel₁ = mediating-map/ (Ω-is-set fe pe) r p

   extension-rel-triangle₁ : extension-rel₁ ∘ η/ ∼ r
   extension-rel-triangle₁ = universality-triangle/ (Ω-is-set fe pe) r p

  module _ (r : X → X → Ω 𝓣)
           (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → r x y ≡ r x' y')
         where

   abstract
    private
     p' : (x : X) {y y' : X} → y ≈ y' → r x y ≡ r x y'
     p' x {y} {y'} = p (≈r x)

     r₁ : X → X / ≋ → Ω 𝓣
     r₁ x = extension-rel₁ (r x) (p' x)

     δ : {x x' : X} → x ≈ x' → (y : X) → r₁ x (η/ y) ≡ r₁ x' (η/ y)
     δ {x} {x'} e y =
       r₁ x (η/ y)  ≡⟨ extension-rel-triangle₁ (r x) (p (≈r x)) y        ⟩
       r  x     y   ≡⟨ p e (≈r y)                                        ⟩
       r  x'    y   ≡⟨ (extension-rel-triangle₁ (r x') (p (≈r x')) y) ⁻¹ ⟩
       r₁ x' (η/ y) ∎

     ρ : (q : X / ≋) {x x' : X} → x ≈ x' → r₁ x q ≡ r₁ x' q
     ρ q {x} {x'} e = /-induction (λ p → r₁ x p ≡ r₁ x' p)
                        (λ q → Ω-is-set fe pe) (δ e) q

     r₂ : X / ≋ → X / ≋ → Ω 𝓣
     r₂ = mediating-map/ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                         (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

     σ : (x : X) → r₂ (η/ x) ≡ r₁ x
     σ = universality-triangle/ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                                (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

     τ : (x y : X) → r₂ (η/ x) (η/ y) ≡ r x y
     τ x y = r₂ (η/ x) (η/ y) ≡⟨ happly (σ x) (η/ y) ⟩
             r₁ x      (η/ y) ≡⟨ extension-rel-triangle₁ (r x) (p' x) y ⟩
             r  x          y  ∎

   extension-rel₂ : X / ≋ → X / ≋ → Ω 𝓣
   extension-rel₂ = r₂

   extension-rel-triangle₂ : (x y : X) → extension-rel₂ (η/ x) (η/ y) ≡ r x y
   extension-rel-triangle₂ = τ

\end{code}

For proving properties of an extended binary relation, it is useful to have a
binary and ternary versions of quotient induction.

\begin{code}

  /-induction₂ : ∀ {𝓦} {P : X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' : X / ≋) → is-prop (P x' y'))
               → ((x y : X) → P (η/ x) (η/ y))
               → (x' y' : X / ≋) → P x' y'
  /-induction₂ p h =
   /-induction _ (λ x' → Π-is-prop fe (p x'))
                 (λ x → /-induction' (p (η/ x)) (h x))

  /-induction₃ : ∀ {𝓦} {P : X / ≋ → X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' z' : X / ≋) → is-prop (P x' y' z'))
               → ((x y z : X) → P (η/ x) (η/ y) (η/ z))
               → (x' y' z' : X / ≋) → P x' y' z'
  /-induction₃ p h =
   /-induction₂ (λ x' y' → Π-is-prop fe (p x' y'))
                (λ x y → /-induction' (p (η/ x) (η/ y)) (h x y))


quotients-equivalent : (X : 𝓤 ̇ ) (R : EqRel {𝓤} {𝓥} X) (R' : EqRel {𝓤} {𝓦} X)
                     → ({x y : X} → x ≈[ R ] y ⇔ x ≈[ R' ] y)
                     → (X / R) ≃ (X / R')
quotients-equivalent X (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
                       (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t') ε = γ
 where
  ≋  = (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
  ≋' = (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t')

  i : {x y : X} → x ≈ y → η/ ≋' x ≡ η/ ≋' y
  i e = η/-identifies-related-points ≋' (lr-implication ε e)

  i' : {x y : X} → x ≈' y → η/ ≋ x ≡ η/ ≋ y
  i' e = η/-identifies-related-points ≋ (rl-implication ε e)

  f : X / ≋ → X / ≋'
  f = mediating-map/ ≋ (quotient-is-set ≋') (η/ ≋') i

  f' : X / ≋' → X / ≋
  f' = mediating-map/ ≋' (quotient-is-set ≋) (η/ ≋) i'

  a : (x : X) → f (f' (η/ ≋' x)) ≡ η/ ≋' x
  a x = f (f' (η/ ≋' x)) ≡⟨ I ⟩
        f (η/ ≋ x)       ≡⟨ II ⟩
        η/ ≋' x          ∎
   where
    I  = ap f (universality-triangle/ ≋' (quotient-is-set ≋) (η/ ≋) i' x)
    II = universality-triangle/ ≋ (quotient-is-set ≋') (η/ ≋') i x

  α : f ∘ f' ∼ id
  α = /-induction ≋' (λ u → f (f' u) ≡ u) (λ u → quotient-is-set ≋') a

  a' : (x : X) → f' (f (η/ ≋ x)) ≡ η/ ≋ x
  a' x = f' (f (η/ ≋ x)) ≡⟨ I ⟩
        f' (η/ ≋' x)     ≡⟨ II ⟩
        η/ ≋ x           ∎
   where
    I  = ap f' (universality-triangle/ ≋ (quotient-is-set ≋') (η/ ≋') i x)
    II = universality-triangle/ ≋' (quotient-is-set ≋) (η/ ≋) i' x

  α' : f' ∘ f ∼ id
  α' = /-induction ≋ (λ u → f' (f u) ≡ u) (λ u → quotient-is-set ≋) a'


  γ : (X / ≋) ≃ (X / ≋')
  γ = qinveq f (f' , α' , α)

\end{code}

Added 15 March 2022 by Tom de Jong, after discussion with Martín.

If we have pushouts and univalence, then images of maps from small types to
locally small types are small, as proved by Egbert Rijke in
https://arxiv.org/abs/1701.07538

We can also take the result on small images as a stand-alone assumption, which
is what we do here.

We show, under this assumption, that quotients of small types by small-valued
equivalence relations are small again, as observed by Rijke in Corollary 5.1 of
the above paper.

\begin{code}

open import UF-Size
open SmallImages pt

module _
        (X : 𝓤 ̇  )
        (_≈_ : X → X → 𝓤 ̇  )
        (≈p  : is-prop-valued _≈_)
        (≈r  : reflexive _≈_)
        (≈s  : symmetric _≈_)
        (≈t  : transitive _≈_)
       where

 open quotient X _≈_ ≈p ≈r ≈s ≈t

 open import UF-Equiv
 open import UF-EquivalenceExamples

 set-quotient-is-small : Small-Set-Images 𝓤 → is-small X/≈
 set-quotient-is-small smi = smi equiv-rel (powersets-are-sets fe pe) γ
  where
   γ : is-locally-small (X → Ω 𝓤)
   γ f g = S , ≃-sym e
    where
     S : 𝓤 ̇
     S = (x : X) → f x holds ⇔ g x holds
     e = (f ≡ g) ≃⟨ ≃-funext fe f g ⟩
         f ∼ g   ≃⟨ I ⟩
         S       ■
      where
       I = Π-cong fe fe X (λ x → f x ≡ g x) (λ x → f x holds ⇔ g x holds) II
        where
         II : (x : X) → (f x ≡ g x) ≃ (f x holds ⇔ g x holds)
         II x = logically-equivalent-props-are-equivalent
                 (Ω-is-set fe pe)
                 (×-is-prop (Π-is-prop fe (λ _ → holds-is-prop (g x)))
                            (Π-is-prop fe (λ _ → holds-is-prop (f x))))
                 (λ p → transport _holds p , back-transport _holds p)
                 (λ (u , v) → Ω-extensionality fe pe u v)

 set-quotient-is-small' : Small-Images 𝓤 → is-small X/≈
 set-quotient-is-small' =
  set-quotient-is-small ∘ Small-Set-Images-from-Small-Images

\end{code}

Added 22 March 2022.

We now prove the converse. That is, given small set quotients, we get small
images of maps to locally small sets.

\begin{code}

open import UF-ImageAndSurjection
open ImageAndSurjection pt
open PropositionalTruncation pt

module small-images-construction
        {X : 𝓤 ̇  }
        {Y : 𝓤 ⁺ ̇  }
        (f : X → Y)
        (Y-is-set : is-set Y)
        (Y-is-loc-small : is-locally-small Y)
       where

 _≈_ : X → X → 𝓤 ⁺ ̇
 x ≈ x' = f x ≡ f x'

 ≈-is-prop-valued : is-prop-valued _≈_
 ≈-is-prop-valued x x' = Y-is-set

 ≈-is-reflexive : reflexive _≈_
 ≈-is-reflexive x = refl

 ≈-is-symmetric : symmetric _≈_
 ≈-is-symmetric x x' p = p ⁻¹

 ≈-is-transitive : transitive _≈_
 ≈-is-transitive _ _ _ p q = p ∙ q

 ≈-is-equiv-rel : is-equiv-relation _≈_
 ≈-is-equiv-rel = ≈-is-prop-valued , ≈-is-reflexive  ,
                  ≈-is-symmetric   , ≈-is-transitive

\end{code}

Using that Y is locally small, we resize _≈_ down to a 𝓤-valued equivalence
relation.

\begin{code}

 _≈⁻_ : X → X → 𝓤 ̇
 x ≈⁻ x' = pr₁ (Y-is-loc-small (f x) (f x'))

 ≈⁻-≃-≈ : {x x' : X} → x ≈⁻ x' ≃ x ≈ x'
 ≈⁻-≃-≈ {x} {x'} = pr₂ (Y-is-loc-small (f x) (f x'))

 ≈⁻-is-prop-valued : is-prop-valued _≈⁻_
 ≈⁻-is-prop-valued x x' = equiv-to-prop ≈⁻-≃-≈ (≈-is-prop-valued x x')

 ≈⁻-is-reflexive : reflexive _≈⁻_
 ≈⁻-is-reflexive x = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-reflexive x)

 ≈⁻-is-symmetric : symmetric _≈⁻_
 ≈⁻-is-symmetric x x' p = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-symmetric x x' (⌜ ≈⁻-≃-≈ ⌝ p))

 ≈⁻-is-transitive : transitive _≈⁻_
 ≈⁻-is-transitive x x' x'' p q =
  ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-transitive x x' x'' (⌜ ≈⁻-≃-≈ ⌝ p) (⌜ ≈⁻-≃-≈ ⌝ q))

 ≈⁻-is-equiv-rel : is-equiv-relation _≈⁻_
 ≈⁻-is-equiv-rel = ≈⁻-is-prop-valued , ≈⁻-is-reflexive  ,
                   ≈⁻-is-symmetric   , ≈⁻-is-transitive

 ≈R : EqRel X
 ≈R = _≈_ , ≈-is-equiv-rel

 X/≈ : 𝓤 ⁺⁺ ̇
 X/≈ = (X / ≈R)

 X/≈⁻ : 𝓤 ⁺ ̇
 X/≈⁻ = (X / (_≈⁻_ , ≈⁻-is-equiv-rel))

 [_] : X → X/≈
 [_] = η/ ≈R

 X/≈-≃-X/≈⁻ : X/≈ ≃ X/≈⁻
 X/≈-≃-X/≈⁻ = quotients-equivalent X ≈R (_≈⁻_ , ≈⁻-is-equiv-rel)
                                        (⌜ ≈⁻-≃-≈ ⌝⁻¹ , ⌜ ≈⁻-≃-≈ ⌝)

\end{code}

We now proceed to show that X/≈ and image f are equivalent types.

\begin{code}

 corestriction-respects-≈ : {x x' : X}
                          → x ≈ x'
                          → corestriction f x ≡ corestriction f x'
 corestriction-respects-≈ =
  to-subtype-≡ (λ y → being-in-the-image-is-prop y f)

 quotient-to-image : X/≈ → image f
 quotient-to-image = mediating-map/ ≈R (image-is-set f Y-is-set)
                      (corestriction f) (corestriction-respects-≈)

 image-to-quotient' : (y : image f)
                    → Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ pr₁ y)
 image-to-quotient' (y , p) = ∥∥-rec prp r p
  where
   r : (Σ x ꞉ X , f x ≡ y)
     → (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
   r (x , e) = [ x ] , ∣ x , refl , e ∣
   prp : is-prop (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
   prp (q , u) (q' , u') = to-subtype-≡ (λ _ → ∃-is-prop)
                                        (∥∥-rec₂ (quotient-is-set (≈R)) γ u u')
    where
     γ : (Σ x  ꞉ X , ([ x  ] ≡ q ) × (f x  ≡ y))
       → (Σ x' ꞉ X , ([ x' ] ≡ q') × (f x' ≡ y))
       → q ≡ q'
     γ (x , refl , e) (x' , refl , refl) = η/-identifies-related-points ≈R e

 image-to-quotient : image f → X/≈
 image-to-quotient y = pr₁ (image-to-quotient' y)

 image-to-quotient-lemma : (x : X)
                         → image-to-quotient (corestriction f x) ≡ [ x ]
 image-to-quotient-lemma x = ∥∥-rec (quotient-is-set ≈R) γ t
  where
   q : X/≈
   q = image-to-quotient (corestriction f x)
   t : ∃ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x)
   t = pr₂ (image-to-quotient' (corestriction f x))
   γ : (Σ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x))
     → q ≡ [ x ]
   γ (x' , u , v) =   q    ≡⟨ u ⁻¹ ⟩
                    [ x' ] ≡⟨ η/-identifies-related-points ≈R v ⟩
                    [ x  ] ∎

 image-≃-quotient : image f ≃ X/≈
 image-≃-quotient = qinveq ϕ (ψ , ρ , σ)
  where
   ϕ : image f → X/≈
   ϕ = image-to-quotient
   ψ : X/≈ → image f
   ψ = quotient-to-image
   τ : (x : X) → ψ [ x ] ≡ corestriction f x
   τ = universality-triangle/ ≈R (image-is-set f Y-is-set)
                              (corestriction f)
                              corestriction-respects-≈
   σ : ϕ ∘ ψ ∼ id
   σ = /-induction ≈R _ (λ q → quotient-is-set ≈R) γ
    where
     γ : (x : X) → ϕ (ψ [ x ]) ≡ [ x ]
     γ x = ϕ (ψ [ x ])            ≡⟨ ap ϕ (τ x)                ⟩
           ϕ (corestriction f x ) ≡⟨ image-to-quotient-lemma x ⟩
           [ x ]                  ∎
   ρ : ψ ∘ ϕ ∼ id
   ρ (y , p) = ∥∥-rec (image-is-set f Y-is-set) γ p
    where
     γ : (Σ x ꞉ X , f x ≡ y) → ψ (ϕ (y , p)) ≡ (y , p)
     γ (x , refl) = ψ (ϕ (f x , p))           ≡⟨ ⦅1⦆ ⟩
                    ψ (ϕ (corestriction f x)) ≡⟨ ⦅2⦆ ⟩
                    ψ [ x ]                   ≡⟨ ⦅3⦆ ⟩
                    corestriction f x         ≡⟨ ⦅4⦆ ⟩
                    (f x , p)                 ∎
      where
       ⦅4⦆ = to-subtype-≡ (λ y → being-in-the-image-is-prop y f) refl
       ⦅1⦆ = ap (ψ ∘ ϕ) (⦅4⦆ ⁻¹)
       ⦅2⦆ = ap ψ (image-to-quotient-lemma x)
       ⦅3⦆ = τ x

\end{code}

And finally, the promised result: small set quotients yield small images of maps
to locally small sets.

\begin{code}

Small-Set-Quotients : (𝓤 : Universe) → 𝓤 ⁺ ̇
Small-Set-Quotients 𝓤 = {X : 𝓤 ̇  } (R : EqRel {𝓤} {𝓤} X) → is-small (X / R)

Small-Set-Images-from-Small-Set-Quotients : Small-Set-Quotients 𝓤
                                          → Small-Set-Images 𝓤
Small-Set-Images-from-Small-Set-Quotients h f Y-is-set Y-is-loc-small =
 ≃-size-contravariance e (h (_≈⁻_ , ≈⁻-is-equiv-rel))
  where
   open small-images-construction f Y-is-set Y-is-loc-small
   e = image f ≃⟨ image-≃-quotient ⟩
       X/≈     ≃⟨ X/≈-≃-X/≈⁻       ⟩
       X/≈⁻    ■

\end{code}
