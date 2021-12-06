# let pr x = print x; print "\n"; x in

let flip f x y = f y x in

let rec
foldl f x xs =
  case xs
  | x':xs' -> foldl f (f x x') xs'
  | []     -> x
in foldl (flip (:)) [] [1,2,3]
