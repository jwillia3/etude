let pr x = print x; print "\n"; x
let flip f x y = f y x
let . f g x = f (g x)
let $ f x = f x

let rec foldl f x xs = case xs
                       | x':xs' -> foldl f (f x x') xs'
                       | []     -> x

let reverse xs = foldl (flip (:)) [] xs

let rec foldr f x xs = foldl (flip f) x (reverse xs)

let concat xs ys = foldr (:) ys xs
let append x xs = concat xs [x]
let flatten xss = foldr (concat) [] xss

let map f xs = foldr ((:) . f) [] xs
let flatmap f xs = flatten (map f xs)

let implode strings = foldr (^) "" strings
