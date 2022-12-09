{-# OPTIONS --guardedness #-}

module day-1 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
import Data.List using (reverse)
open import Data.Maybe
open import Data.Nat using (_≤_)
open import Data.Nat.Show
open import Relation.Nullary
open import Relation.Binary
open import IO

_s∷_ : String → String → String
a s∷ b = primStringAppend a b

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

digit : Char → Maybe Nat
digit '0' = just 0
digit '1' = just 1
digit '2' = just 2
digit '3' = just 3
digit '4' = just 4
digit '5' = just 5
digit '6' = just 6
digit '7' = just 7
digit '8' = just 8
digit '9' = just 9
digit _ = nothing

parseLine : Maybe String → Line
parseLine nothing = empty
parseLine (just s) = go nothing (mapList digit (Data.List.reverse (primStringToList s)))
  where
  go : Maybe Nat → List (Maybe Nat) → Line
  go nothing [] = empty
  go nothing (nothing ∷ xs) = go nothing xs
  go nothing ((just n) ∷ xs) = go (just n) xs
  go (just n) [] = item n
  go (just n) (nothing ∷ xs) = go (just (n * 10)) xs {- should this have * 10 ? -}
  go (just n) ((just n₂) ∷ xs) = go (just ((n * 10) + n₂)) xs

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
splitElves s = Data.List.reverse (go [] nothing (splitLines s))
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
showLines (n ∷ r) = (showLine n) s∷ ("," s∷ (showLines r))

showList : List Nat → String
showList [] = ""
showList (n ∷ r) = (show n) s∷ ("," s∷ (showList r))

findMax : List Nat → Maybe Nat
findMax [] = nothing
findMax nr = go 0 0 nothing nr
  where
  go : Nat → Nat → Maybe Nat → List Nat → Maybe Nat
  go idx mval nothing [] = nothing
  go idx mval midx [] = midx
  go idx mval midx (n ∷ nr) with (n Data.Nat.≥? mval)
  ...                       | yes _ = go (idx + 1) n (just idx) nr
  ...                       | no _ = go (idx + 1) mval midx nr

showMaybe : Maybe Nat → String
showMaybe nothing = "nothing"
showMaybe (just n) = show n

takeAt : List Nat → Nat → Maybe Nat
takeAt [] _ = nothing
takeAt (n ∷ nr) 0 = just n
takeAt (n ∷ nr) (suc i) = takeAt nr i

{- main -}
main : Main
main with splitElves "1000\n2000\n3000\n\n4000\n\n5000\n6000\n\n7000\n8000\n9000\n\n10000\n"
... | [] = run (putStrLn "no elves")
... | elves with findMax elves
...         | nothing = run (putStrLn "no rich elves")
...         | just idx = run (putStrLn ("elf " s∷ ((show (idx + 1)) s∷ (" has " s∷ ((showMaybe (takeAt elves idx)) s∷ " calories.")))))

{- main = run (putStrLn (showLines (splitLines "1000\n2000\n\n3000\n\n4000\n"))) -}
{- main = run (putStrLn (showList (splitElves "1000\n2000\n\n3000\n\n4000\n"))) -}
{- main = run (putStrLn (showLines (splitLines "1000\n2000\n\n3000\n\n4000\n"))) -}
