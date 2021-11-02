var INet = require("./inet.js");

var inet = INet(`
(node Dup 3)
(node Con 3)

(ctor S 1)
(ctor Z 0)
(func Add 2)
(func Double 1)

(ctor T 0)
(ctor F 0)
(func Not 1)
(func And 2)
(func If 3)

(ctor O 1)
(ctor I 1)
(ctor E 0)
(func Inc 1)
(func Sum 2)
(node Sum_E 2)
(node Sum_O 3)
(node Sum_I 3)
(func Bus 2)

(rule Con Dup (Con <1 y x) (Con <2 w z) (Dup >1 y w) (Dup >2 x z))
(rule Con Con (<1 >1) (<2 >2))

(rule Dup E (E <1) (E <2))
(rule Dup O (Dup >1 x y) (O <1 x) (O <2 y))
(rule Dup I (Dup >1 x y) (I <1 x) (I <2 y))

(rule Dup Z (Z <1) (Z <2))
(rule Dup S (Dup >1 x y) (S <1 x) (S <2 y))

(case (Add (S a) b) (Add a (S b)))
(case (Add Z     b) b)

(case (Double (S a)) (S (S (Double a))))
(case (Double (Z))   (Z))

(rule Bus Z (Inc <1 <2))
(rule Bus S (Dup >1 p0 p1) (Bus p0 <1 br) (Bus p1 br <2))

(case (Not (T)) (F))
(case (Not (F)) (T))

(case (And (T) y) y)
(case (And (F) y) (F))

(case (Inc (E)) (E))
(case (Inc (O x)) (I x))
(case (Inc (I x)) (O (Inc x)))

(case (If (T) t f) t)
(case (If (F) t f) f)

(case (Sum (E)   (E))   (E))
(case (Sum (E)   (O b)) (O b))
(case (Sum (E)   (I b)) (I b))
(case (Sum (O a) (E))   (O a))
(case (Sum (O a) (O b)) (O (Sum a b)))
(case (Sum (O a) (I b)) (I (Sum a b)))
(case (Sum (I a) (E))   (I a))
(case (Sum (I a) (O b)) (I (Sum a b)))
(case (Sum (I a) (I b)) (O (Inc (Sum a b))))
`);

//(rule Sum E (Sum_E <1 <2))
//(rule Sum_E E (E <1))
//(rule Sum E (Sum_E <1 <2))
//(rule Sum_E O (O <1 >1))
//(rule Sum E (Sum_E <1 <2))
//(rule Sum_E I (I <1 >1))
//(rule Sum O (Sum_O <1 <2 >1))
//(rule Sum_O E (O <1 <2))
//(rule Sum O (Sum_O <1 <2 >1))
//(rule Sum_O O (Sum <2 >1 $0) (O <1 $0))
//(rule Sum O (Sum_O <1 <2 >1))
//(rule Sum_O I (Sum <2 >1 $0) (I <1 $0))
//(rule Sum I (Sum_I <1 <2 >1))
//(rule Sum_I E (I <1 <2))
//(rule Sum I (Sum_I <1 <2 >1))
//(rule Sum_I O (Sum <2 >1 $0) (I <1 $0))
//(rule Sum I (Sum_I <1 <2 >1))
//(rule Sum_I O (Sum <2 >1 $1) (Inc $1 $0) (O <1 $0))



var mem = inet.read_tree("(Add (S (S (S (Z)))) (S (S (Z))))");
var mem = inet.read_tree("(Not (Not (Not (T))))");
var mem = inet.read_tree("(If (T) (S Z) Z)");
var mem = inet.read_tree("(Double (S (S (S (Z)))))");
var mem = inet.read_tree("(Bus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (Z))))))))))))))))))))) (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O (O E)))))))))))))))))))))))))))))))))");
//var mem = inet.read_tree("(Sum (I (I (O (O (E))))) (O (I (O (O (E))))))");

inet.find_redexes(mem);
console.log(inet.show_tree(mem));

var step = 0;
while (mem.red.length > 0 && step < 10000000) {
  inet.reduce_step(mem);
  ++step;
}
//console.log(inet.show(mem));

console.log(inet.show_tree(mem));
console.log("rewrites:", mem.rwt);
