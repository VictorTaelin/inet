var K = 0;

function O(bits) {
  return {_: "O", pred: bits};
}

function I(bits) {
  return {_: "I", pred: bits};
}

const E = {_: "E"};

function S(pred) {
  return {_: "S", pred};
}

const Z = {_: "Z"};

function Inc(bits) {
  ++K;
  switch (bits._) {
    case "O": return I(bits.pred);
    case "I": return O(Inc(bits.pred));
    case "E": return E;
  }
}

function Dup(val) {
  switch (val._) {
    case "O": var [x,y] = Dup(val.pred); return [O(x),O(y)];
    case "I": var [x,y] = Dup(val.pred); return [I(x),I(y)];
    case "S": var [x,y] = Dup(val.pred); return [S(x),S(y)];
    case "E": return [E,E];
    case "Z": return [Z,Z];
  }
}
  
function Bus(n, bs) {
  switch (n._) {
    case "Z": return Inc(bs);
    case "S": var [p0,p1] = Dup(n.pred); return Bus(p0, Bus(p1, bs));
  }
}

function show(bits) {
  switch (bits._) {
    case "O": return "0" + show(bits.pred);
    case "I": return "1" + show(bits.pred);
    case "E": return "";
  }
}

const O16 = O(O(O(O(O(O(O(O(O(O(O(O(O(O(O(O(E))))))))))))))));
const O32 = O(O(O(O(O(O(O(O(O(O(O(O(O(O(O(O(O16))))))))))))))));
const N0  = Z;
const N1  = S(N0);
const N2  = S(N1);
const N3  = S(N2);
const N4  = S(N3);
const N5  = S(N4);
const N6  = S(N5);
const N7  = S(N6);
const N8  = S(N7);
const N9  = S(N8);
const N10 = S(N9);
const N11 = S(N10);
const N12 = S(N11);
const N13 = S(N12);
const N14 = S(N13);
const N15 = S(N14);
const N16 = S(N15);
const N17 = S(N16);
const N18 = S(N17);
const N19 = S(N18);
const N20 = S(N19);
const N21 = S(N20);
const N22 = S(N21);
const N23 = S(N22);
const N24 = S(N23);
const N25 = S(N24);
const N26 = S(N25);
const N27 = S(N26);
const N28 = S(N27);
const N29 = S(N28);
const N30 = S(N29);
const N31 = S(N30);
const N32 = S(N31);


console.log(show(Bus(N25, O32)));
console.log(K);
