var INet = require("./inet.js");

var inet = INet(`
(kind Dup 3)
(kind Con 3)
(kind Suc 2)
(kind Zer 1)
(kind Add 3)
(kind Tru 1)
(kind Fal 1)
(kind Not 2)
(kind Bi0 2)
(kind Bi1 2)
(kind BiE 1)
(kind Inc 2)
(kind All 2)
(kind Par 3)
(kind Iff 4)
(kind Foo 2)
(kind Arg 2)
(kind And 3)
(kind Bus 3)
(rule Con Dup (Con <1 y x) (Con <2 w z) (Dup 1> y w) (Dup 2> x z))
(rule Con Con (<1 1>) (<2 2>))
(rule Add Suc (Add 1> x <2) (Suc x <1))
(rule Add Zer (<1 <2))
(rule Bus Zer (Inc <1 <2))
(rule Bus Suc (Dup 1> p0 p1) (Bus p0 <1 br) (Bus p1 br <2))
(rule Not Tru (Fal <1))
(rule Not Fal (Tru <1))
(rule And Tru (<1 <2))
(rule And Fal (Fal <2) (<1 <1))
(rule Inc BiE (BiE <1))
(rule Inc Bi0 (Bi1 <1 1>))
(rule Inc Bi1 (Bi0 <1 x) (Inc 1> x))
(rule All BiE (Tru <1))
(rule All Bi0 (Fal <1) (1> 1>))
(rule All Bi1 (All 1> <1))
(rule Dup BiE (BiE <1) (BiE <2))
(rule Dup Bi0 (Dup 1> x y) (Bi0 <1 x) (Bi0 <2 y))
(rule Dup Bi1 (Dup 1> x y) (Bi1 <1 x) (Bi1 <2 y))
(rule Dup Zer (Zer <1) (Zer <2))
(rule Dup Suc (Dup 1> x y) (Suc <1 x) (Suc <2 y))
(rule Iff Tru (<3 <1) (<2 <2))
(rule Iff Fal (<3 <2) (<1 <1))
(rule Suc Suc (<1 1>))
(rule Bi0 Bi0 (<1 1>))
(rule Zer Zer)
(rule Foo Arg
  (Dup 1> x0 x1)
  (Iff cond tk csef <1)
  (All x0 cond)
  (Tru tk)
  (Inc x1 xi)
  (Arg kk xi)
  (Foo kk csef))
`);


//(Pow (Suc n)) = (

//    1    2     3     4
//iff cond cse_t cse_f ret

//(foo x) = (if (all x) x (foo (inc x)))

//(all be    ) = true
//(all (b1 x)) = (all x)
//(all (b0 x)) = false

//a2 - Inc - Bi1 - b2
//a2 - Bi0 - Inc - b2

//var mem = inet.read(`
//Rot R
//Con R a b
//Dup x a b
//Con x y y
//`);

var mem = inet.read(`
Rot Z
Inc N Z
Inc M N
Inc L M
Inc K L
Inc J K
Inc I J
Inc H I
Inc G H
Inc F G
Inc E F
Inc D E
Inc C D
Inc B C
Inc A B
Inc a A
Bi0 a b
Bi0 b c
Bi0 c d
Bi0 d e
BiE e
`);

//var mem = inet.read(`
//Rot R
//Foo A R
//Arg A a
//Bi0 a b
//Bi0 b c
//BiE c
//`);

//var mem = inet.read(`
//Rot R
//All a R
//Bi0 a b
//Bi0 b c
//Bi0 c d
//Bi0 d e
//BiE e
//`);
//
var mem = inet.read(`
Rot R
And A B R
Tru A
Tru B
`);

var mem = inet.read(`
Rot Z
Bus a A Z
Bi0 A B
Bi0 B C
Bi0 C D
Bi0 D E
Bi0 E F
Bi0 F G
Bi0 G H
Bi0 H I
Bi0 I J
Bi0 J K
Bi0 K L
Bi0 L M
Bi0 M N
Bi0 N O
Bi0 O P
Bi0 P Q
Bi0 Q R
Bi0 R S
Bi0 S T
Bi0 T U
Bi0 U V
Bi0 V W
Bi0 W X
Bi0 X Y
Bi0 Y Z
Bi0 Z AA
Bi0 AA AB
Bi0 AB AC
Bi0 AC AD
Bi0 AD AE
Bi0 AE AF
Bi0 AF AG
BiE AG
Suc a b
Suc b c
Suc c d
Suc d e
Suc e f
Suc f g
Suc g h
Suc h i
Suc i j
Suc j k
Suc k l
Suc l m
Suc m n
Suc n o
Suc o p
Suc p q
Suc q r
Suc r s
Zer s
`);

inet.find_redexes(mem);
console.log(inet.show(mem));

var step = 0;
while (mem.red.length > 0 && step < 1000000) {
  //console.log("step " + step + ":");
  inet.reduce_step(mem);
  //console.log(inet.show(mem));
  ++step;
}
console.log(inet.show(mem));
console.log(mem.rwt);

//inet.init_red(mem);
//inet.reduce_step(mem);
//console.log(inet.show(mem));

//console.log(inet.show(mem));
//console.log("Done in " + steps + " steps.");
