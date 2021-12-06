let pr x = print x; print "\n"; x
let flip f x y = f y x
let . f g x = f (g x)
let $ f x = f x

let rec foldl f x xs = case xs
                       | x':xs' -> foldl f (f x x') xs'
                       | []     -> x

let reverse xs = foldl (flip (:)) [] xs

let rec foldr f x xs = foldl (flip f) x (reverse xs)

let map f xs = foldr ((:) . f) [] xs

let _ = pr $ map (+ 1) [100, 20, 3]
