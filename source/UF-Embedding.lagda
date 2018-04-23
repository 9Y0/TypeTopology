\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Embedding where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-Equiv
open import UF-Retracts
open import UF-Subsingletons-Retracts
open import UF-Equiv
open import UF-LeftCancellable
open import UF-Yoneda

isEmbedding : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEmbedding f = ∀ y → isProp(fiber f y)

embedding-lc : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding f → left-cancellable f
embedding-lc f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

isEmbedding' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEmbedding' f = ∀ x x' → isEquiv (ap f {x} {x'})

embedding-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding f → isEmbedding' f
embedding-embedding' {U} {V} {X} {Y} f ise = g
 where
  b : (x : X) → isSingleton(fiber f (f x))
  b x = (x , idp (f x)) , ise (f x) (x , idp (f x))
  c : (x : X) → isSingleton(fiber' f (f x))
  c x = retract-of-singleton (pr₁ (fiber-lemma f (f x))) (pr₁(pr₂(fiber-lemma f (f x)))) (b x)
  g : (x x' : X) → isEquiv(ap f {x} {x'})
  g x = universality-equiv x refl (unique-element-is-universal-element
                                         (λ x' → f x ≡ f x')
                                         (pr₁(c x))
                                         (pr₂(c x))) 

embedding'-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding' f → isEmbedding f
embedding'-embedding {U} {V} {X} {Y} f ise = g
 where
  e : (x x' : X) → is-the-only-element (x , idp (f x))
  e x x' = universal-element-is-the-only-element
             (x , idp (f x))
             (equiv-universality x (idp (f x)) (ise x))
  h : (x : X) → isProp (fiber' f (f x))
  h x σ τ = σ ≡⟨ (e x (pr₁ σ) σ)⁻¹ ⟩ (x , idp (f x)) ≡⟨ e x (pr₁ τ) τ ⟩ τ ∎  
  g' : (y : Y) → isProp (fiber' f y)
  g' y (x , p) = transport (λ y → isProp (Σ \(x' : X) → y ≡ f x')) (p ⁻¹) (h x) (x , p)
  g : (y : Y) → isProp (fiber f y)
  g y = left-cancellable-reflects-isProp
            (pr₁ (fiber-lemma f y))
            (section-lc _ (pr₂ (pr₂ (fiber-lemma f y)))) (g' y)

pr₁-embedding : ∀ {U V} {X : U ̇} {Y : X → V ̇}
              → ((x : X) → isProp(Y x))
              → isEmbedding (pr₁ {U} {V} {X} {Y})
pr₁-embedding f x ((.x , y') , refl) ((.x , y'') , refl) = g
 where
  g : (x , y') , refl ≡ (x , y'') , refl
  g = ap (λ y → (x , y) , refl) (f x y' y'')

pr₁-lc-bis : ∀ {U V} {X : U ̇} {Y : X → V ̇} → ({x : X} → isProp(Y x)) → left-cancellable pr₁
pr₁-lc-bis f {u} {v} r = embedding-lc pr₁ (pr₁-embedding (λ x → f {x})) r

pr₁-embedding-converse : ∀ {U V} {X : U ̇} {Y : X → V ̇}
                       → isEmbedding (pr₁ {U} {V} {X} {Y})
                       → ((x : X) → isProp(Y x))
pr₁-embedding-converse {U} {V} {X} {Y} ie x = go
  where
    e : Σ Y → X
    e = pr₁ {U} {V} {X} {Y}
    isp : isProp(fiber e x)
    isp = ie x
    s : Y x → fiber e x
    s y = (x , y) , refl
    r : fiber e x → Y x
    r ((x , y) , refl) = y
    rs : (y : Y x) → r(s y) ≡ y
    rs y = refl
    go : isProp(Y x)
    go = left-cancellable-reflects-isProp s (section-lc s (r , rs)) isp

K-idtofun-lc : ∀ {U} → K (U ′) 
            → {X : U ̇} (x y : X) (A : X → U ̇) → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {U} k {X} x y A {p} {q} r = k (Set U) p q

left-cancellable-maps-into-sets-are-embeddings : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y)
                                               → left-cancellable f → isSet Y → isEmbedding f
left-cancellable-maps-into-sets-are-embeddings {U} {V} {X} {Y} f f-lc iss y (x , p) (x' , p') = to-Σ-Id (λ x → f x ≡ y) (r , q)
 where
   r : x ≡ x'
   r = f-lc (p ∙ (p' ⁻¹))
   q : yoneda-nat (λ x → f x ≡ y) p x' r ≡ p'
   q = iss (yoneda-nat (λ x → f x ≡ y) p x' r) p'

left-cancellable-maps-are-embeddings-with-K : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y)
                                            → left-cancellable f → K V → isEmbedding f
left-cancellable-maps-are-embeddings-with-K {U} {V} {X} {Y} f f-lc k = left-cancellable-maps-into-sets-are-embeddings f f-lc (k Y)

id-isEmbedding : ∀ {U} {X : U ̇} → isEmbedding (id {U} {X})
id-isEmbedding = paths-to-isProp

disjoint-images : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → U ⊔ V ⊔ W ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                         → isEmbedding f → isEmbedding g → disjoint-images f g
                         → isEmbedding (cases f g)
disjoint-cases-embedding {U} {V} {W} {X} {Y} {A} f g ef eg d = go
  where
   go : (a : A) (σ τ : Σ \(z : X + Y) → cases f g z ≡ a) → σ ≡ τ
   go a (inl x , p) (inl x' , p') = r
     where
       q : x , p ≡ x' , p'
       q = ef a (x , p) (x' , p')
       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p
       r : inl x , p ≡ inl x' , p'
       r = ap h q
   go a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inr y' , q') = r
     where
       p : y , q ≡ y' , q'
       p = eg a (y , q) (y' , q')
       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q
       r : inr y , q ≡ inr y' , q'
       r = ap h p

\end{code}
