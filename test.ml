let pr x = print x; print "\n"; x in

let rec
foldl f x xs =
  case xs
  | x':xs' -> foldl f (f x x') xs'
  | []     -> x
in foldl (fn x y -> y:x) [] [1,2,3]
