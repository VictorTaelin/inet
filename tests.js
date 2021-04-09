var INet = require("./inet.js");

var inet = INet(`
  (kind Dup 3)
  (kind Con 3)
  (kind Suc 2)
  (kind Zer 1)
  (kind Add 3)
  (rule Con Dup (Con a2 y x) (Con a3 w z) (Dup b2 y w) (Dup b3 x z))
  (rule Con Con (a2 b2) (a3 b3))
  (rule Add Suc (Add b2 x a3) (Suc x a2))
  (rule Add Zer (a2 a3))
`);

var mem = inet.read(`
Rot R
Con R a b
Dup x a b
Con x y y
`);

var mem = inet.read(`
Rot R
Add n m R 
Suc n a
Suc a b
Suc b c
Zer c
Suc m d
Suc d e
Zer e
`);

console.log(mem);

mem.ant.push([inet.new_port(0,1)]);
console.log(inet.show(mem));

for (var i = 0; i < 30; ++i) {
  inet.reduce_step(mem);
  console.log(inet.show(mem));
}

inet.reduce_step(mem);
console.log(inet.show(mem));
