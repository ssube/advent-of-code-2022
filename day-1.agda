{-# OPTIONS --guardedness #-}

module day-1 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
import Agda.Builtin.Nat as Nat
open import Agda.Builtin.String
open import Data.Maybe
open import Data.Nat.Show
open import Relation.Nullary
open import Relation.Binary
open import IO

data Line : Set where
  empty : Line
  item : Nat.Nat → Line

main : Main
main = run (putStrLn "a\n\nb")

{- AOC stuff -}
splitLines : String → List Line
splitLines s = go nothing (primStringToList s)
  where
  go : Maybe (List Line) → List Char → List Line
  go acc [] = []
  go acc ('\n' ∷ ss) = go nothing ss
  go acc (s ∷ ss) = go (just (empty ∷ [])) ss

itemsOnly : Line → Bool
itemsOnly empty = false
itemsOnly (item n) = true

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs) | true  = x ∷ filter p xs
filter p (x ∷ xs) | false = filter p xs

mapList : { A B : Set } → (A → B) → List A → List B
mapList p [] = []
mapList p (x ∷ xs) = (p x) ∷ (mapList p xs)

unline : Line → Nat.Nat
unline empty = 0
unline (item n) = n

splitElves : String → List Nat.Nat
splitElves s = go [] nothing (splitLines s)
  where
  go : List Nat.Nat → Maybe Nat.Nat → List Line → List Nat.Nat
  go acl nothing [] = acl
  go acl nothing (l ∷ ls) = go acl (just (unline l)) ls
  go acl (just acc) [] = acc ∷ acl
  go acl (just acc) (l ∷ ls) = go acl (just (Nat._+_ acc (unline l))) ls