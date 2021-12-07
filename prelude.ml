
let pr x = print x; print "\n"; x
let dbg x = print "DEBUG: "; pr x
let flip f x y = f y x
let . f g x = f (g x)
let $ f x = f x

let not true = false
|   not false = true

let rec foldl f prev (x:xs) = foldl f (f prev x) xs
|       foldl _ prev []     = prev

let reverse xs = foldl (flip (:)) [] xs

let rec foldr f rightmost xs = foldl (flip f) rightmost (reverse xs)

let concat xs ys = foldr (:) ys xs
let append x xs = concat xs [x]
let flatten lists = foldr (concat) [] lists

let map f xs = foldr ((:) . f) [] xs
let flatmap f xs = flatten (map f xs)

let rec app f (x:xs) = f x; app f xs
|       app _ []     = ()

let rec find ok (x:xs) =  if ok then [x] else find ok xs
|       find _  []     =  []

let rec exists ok (x:xs) = ok x || exists ok xs
|       exists _  []     = false

let join strings = foldr (^) "" strings

let isdigit c = ord c >= ord '0' && ord c <= ord '9'
let islower c = ord c >= ord 'a' && ord c <= ord 'z'
let isupper c = ord c >= ord 'A' && ord c <= ord 'Z'
let isalpha c = islower c || isupper c
let isalnum c = isalpha c || isdigit c
let isspace c = c == ' ' || c == '\t' || c == '\n'

let toupper c = if islower c then chr (ord c - 32) else c
let tolower c = if isupper c then chr (ord c + 32) else c

let mapstring f s =
  let rec do i out =
    if i < strlen s then
      do (i + 1) (f (char_at s i) : out)
    else
      implode (reverse out)
  in do 0 []

let touppers s = mapstring toupper s
let tolowers s = mapstring tolower s


let substring i j str =
  let rec do i out =
    if i < j then
      do (i + 1) (char_at str i : out)
    else
      implode (reverse out)
  in
  do i []

let char_in set c =
  let rec do i = i < strlen set && (c == char_at set i || do (i + 1))
  in do 0

let char_to_string c = implode [c]

let atoi s =
  let rec do i out =
    if i < strlen s && isdigit (char_at s i) then
      do (i + 1) (ord (char_at s i) - ord '0' + out * 10)
    else
      out
  in do 0 0

let rec itoa n =
  if n == 0 then "0" else
  if n < 0 then "-" ^ itoa (0 - n) else
  let rec do n out =
    if n == 0 then
      implode out
    else
      do (n / 10) (chr (n rem 10 + ord '0') : out)
  in do n []
