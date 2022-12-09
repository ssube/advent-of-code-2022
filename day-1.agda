{-# OPTIONS --guardedness #-}

module day-1 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
import Data.List using (reverse)
open import Data.Maybe
open import Data.Nat.Show
open import Relation.Nullary
open import Relation.Binary
open import IO

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs) | true  = x ∷ filter p xs
filter p (x ∷ xs) | false = filter p xs

mapList : { A B : Set } → (A → B) → List A → List B
mapList p [] = []
mapList p (x ∷ xs) = (p x) ∷ (mapList p xs)

{- AOC stuff -}
data Line : Set where
  empty : Line
  item : Nat → Line

parseLine : Maybe String → Line
parseLine nothing = empty
parseLine _ = item 0

splitLines : String → List Line
splitLines s = Data.List.reverse (mapList parseLine (go [] nothing (primStringToList s)))
  where
  go : List (Maybe String) → Maybe (List Char) → List Char → List (Maybe String)
  go acl nothing [] = acl
  go acl nothing ('\n' ∷ ss) = go (nothing ∷ acl) nothing ss
  go acl nothing (s ∷ ss) = go acl (just (s ∷ [])) ss
  go acl (just acc) [] = (just (primStringFromList acc)) ∷ acl
  go acl (just acc) ('\n' ∷ ss) = go ((just (primStringFromList acc)) ∷ acl) nothing ss
  go acl (just acc) (s ∷ ss) = go acl (just (s ∷ acc)) ss

isItem : Line → Bool
isItem empty = false
isItem (item n) = true

calories : Line → Nat
calories empty = 0
calories (item n) = n

splitElves : String → List Nat
splitElves s = go [] nothing (splitLines s)
  where
  go : List Nat → Maybe Nat → List Line → List Nat
  go acl nothing []           = acl
  go acl nothing (empty ∷ ls) = go (0 ∷ acl) nothing ls
  go acl nothing (l ∷ ls)     = go acl (just (calories l)) ls
  go acl (just acc) []        = acc ∷ acl
  go acl (just acc) (empty ∷ ls) = go (acc ∷ acl) nothing ls
  go acl (just acc) (l ∷ ls)  = go acl (just (acc + (calories l))) ls

showLine : Line → String
showLine empty = "empty"
showLine (item n) = show n

showLines : List Line → String
showLines [] = ""
showLines (n ∷ r) = primStringAppend (primStringAppend (showLine n) ",") (showLines r)

showList : List Nat → String
showList [] = ""
showList (n ∷ r) = primStringAppend (primStringAppend (show n) ",") (showList r)

{- main -}
main : Main
main = run (putStrLn (showList (splitElves "1000\n2000\n\n3000\n\n4000\n")))

{- main = run (putStrLn (showLines (splitLines "1000\n2000\n\n3000\n\n4000\n"))) -}
