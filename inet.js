// p --|\a        b/|-- s
//     |0|--------|0|
// q --|/          \|-- r
// ======================
// p --x            y-- s
//
// q --y            x-- r

// p --|\a        b/|-- s
//     |1|--------|2|
// q --|/          \|-- r
// ======================
//    n0/|--x  x--|\n3
// p --|2|        |1|-- s
//      \|--y  z--|/
//      /|--z  y--|\
// q --|2|        |1|-- r
//    n1\|--w  w--|/n2

module.exports = function INet(rules) {
  function build_rules(code) {
    function parse_rules(rules) {
      function parse_sexp(str) {
        while (/\s/.test(str[0])) {
          str = str.slice(1);
        }
        if (str[0] === "(") {
          var term = [];
          while (str[0] !== ")") {
            var [str, argm] = parse_sexp(str.slice(1));
            if (argm !== "") {
              term.push(argm);
            }
          }
          return [str.slice(1), term];
        } else {
          var term = "";
          while (str !== "" && /\w/.test(str[0])) {
            term += str[0];
            str = str.slice(1);
          }
          return [str, term];
        }
      };
      return parse_sexp(rules)[1];
    };
    function is_external(var_name) {
      return /[ab][0-8]/.test(var_name);
    }
    function dest_code(dest) {
      if (/[ab][0-8]/.test(dest)) {
        return dest[0]+"_out"+dest[1];
      } else {
        var [i,slot] = dest.split(":");
        //return "new_port(n"+i+"_ptr, "+slot+")";
        return "(((n"+i+"_dest << 4) | "+slot+") >>> 0)";
      }
    }
    function info_code(kind) {
      return kind;
    }
    function flip_nodes(nodes) {
      var new_nodes = [];
      for (var i = 0; i < nodes.length; ++i) {
        new_nodes.push([]);
        for (var j = 0; j < nodes[i].length; ++j) {
          var word = nodes[i][j];
          if (is_external(nodes[i][j])) {
            word = word.replace("a","*").replace("b","a").replace("*","b");
          }
          new_nodes[i].push(word);
        }
      }
      return new_nodes;
    }
    var statements = parse_rules("("+code+")");
    var kinds = {
      Air0: {name: "Air0", arity: 0, kind: 0},
      Air1: {name: "Air1", arity: 1, kind: 1},
      Air2: {name: "Air2", arity: 2, kind: 2},
      Air3: {name: "Air3", arity: 3, kind: 3},
      Air4: {name: "Air4", arity: 4, kind: 4},
      Air5: {name: "Air5", arity: 5, kind: 5},
      Air6: {name: "Air6", arity: 6, kind: 6},
      Air7: {name: "Air7", arity: 7, kind: 7},
      Air8: {name: "Air8", arity: 8, kind: 8},
      Air9: {name: "Air9", arity: 9, kind: 9},
      Air10: {name: "Air10", arity: 10, kind: 10},
      Air11: {name: "Air11", arity: 11, kind: 11},
      Air12: {name: "Air12", arity: 12, kind: 12},
      Air13: {name: "Air13", arity: 13, kind: 13},
      Air14: {name: "Air14", arity: 14, kind: 14},
      Air15: {name: "Air15", arity: 15, kind: 15},
      Rot: {name: "Rot", arity: 1, kind: 16},
    };
    var rules = [];
    for (var statement of statements) {
      switch (statement[0]) {
        case "kind":
          var name = statement[1];
          var arity = Number(statement[2]);
          kinds[name] = {name, arity, kind: Object.keys(kinds).length};
          break;
        case "rule":
          rules.push(statement);
          break;
        default:
          throw "Unknown statement: " + kinds[0];
      }
    }
    //console.log(kinds);
    var cases = "";
    // For each rule on the rule table
    for (var rule of rules) { 
      //console.log("->", JSON.stringify(rule));

      // For both orientations of the rule
      for (var flipped = 0; flipped < 2; ++flipped) {
        // Flips rule if needed
        if (flipped === 0) {
          var a_name = rule[1];
          var b_name = rule[2];
          var nodes = rule.slice(3);
        } else {
          var a_name = rule[2];
          var b_name = rule[1];
          var nodes = flip_nodes(rule.slice(3));
        }

        // Skips if symmetric
        if (a_name === b_name && flipped === 1) {
          continue;
        }

        // Gets active pair kinds (ex: `{name: 'Add', arity: 3, kind: 4}`)
        var a_kind = kinds[a_name];
        var b_kind = kinds[b_name];

        // Builds map of linked ports, both internal and external.
        // Internal ports are represented as 'i:s'
        // - 'i' is the number of the new allocated node
        // - 's' is the slot
        // External ports are represented as 'xN'
        // - 'x' is 'a' if it is neighbor of the first active node, 'b' otherwise
        // - 's' is the slot of the active node that points to that port
        var links = {}; // internal connections
        for (var i = 0; i < nodes.length; ++i) {
          var node = nodes[i];
          if (kinds[node[0]]) {
            for (var i_slot = 1; i_slot < node.length; ++i_slot) {
              if (is_external(node[i_slot])) { // external connection
                links[node[i_slot]] = i + ":" + i_slot;
                links[i + ":" + i_slot] = node[i_slot];
              } else { // internal connection
                if (!links[node[i_slot]]) {
                  links[node[i_slot]] = i + ":" + i_slot;
                } else {
                  var [j,j_slot] = links[node[i_slot]].split(":").map(Number);
                  delete links[node[i_slot]];
                  links[i+":"+i_slot] = j + ":" + j_slot;
                  links[j+":"+j_slot] = i + ":" + i_slot;
                }
              }
            }
          } else {
            links[node[0]] = node[1];
            links[node[1]] = node[0];
          }
        }

        // Builds the case code
        cases += "    case "+(b_kind.kind * rules.length + a_kind.kind)+": // " + a_kind.name+"-"+b_kind.name+";\n";
        cases += "      // gets neighbors\n";
        for (var i = 2; i <= a_kind.arity; ++i) {
          cases += "      a_out"+i+" = mem.val[a_dest+"+i+"];\n"
        }
        for (var i = 2; i <= a_kind.arity; ++i) {
          cases += "      b_out"+i+" = mem.val[b_dest+"+i+"];\n"
        }
        cases += "      // allocs new nodes\n";
        for (var i = 0; i < nodes.length; ++i) {
          var node = nodes[i];
          if (kinds[node[0]]) {
            cases += "      n"+i+"_dest = alloc(mem,"+(kinds[node[0]].arity+1)+");\n";
          }
        }
        cases += "      // fills new nodes\n";
        for (var i = 0; i < nodes.length; ++i) {
          var new_node = nodes[i];
          var new_kind = kinds[new_node[0]];
          if (new_kind) {
            cases += "      mem.val[n"+i+"_dest+0] = "+info_code(new_kind.kind)+";\n";
            for (var slot = 1; slot <= new_kind.arity; ++slot) {
              var var_name = new_node[slot];
              cases += "      mem.val[n"+i+"_dest+"+slot+"] = "+dest_code(links[i+":"+slot])+";\n";
            }
          }
        }
        cases += "      // turns old nodes into air\n";
        cases += "      mem.val[a_dest] = "+info_code(a_kind.arity)+";\n";
        cases += "      mem.val[b_dest] = "+info_code(b_kind.arity)+";\n";
        cases += "      // points air ports to new destinations\n";
        for (var slot = 2; slot <= a_kind.arity; ++slot) {
          cases += "      mem.val[a_dest+"+slot+"] = "+dest_code(links["a"+slot])+";\n";
        }
        for (var slot = 2; slot <= b_kind.arity; ++slot) {
          cases += "      mem.val[b_dest+"+slot+"] = "+dest_code(links["b"+slot])+";\n";
        }
        cases += "      // attaches external ports\n";
        for (var slot = 2; slot <= a_kind.arity; ++slot) {
          cases += "      attach(mem, a_out"+slot+");\n";
        }
        for (var slot = 2; slot <= b_kind.arity; ++slot) {
          cases += "      attach(mem, b_out"+slot+");\n";
        }
        cases += "      // attaches internal ports that must point to external ports\n";
        for (var i = 0; i < nodes.length; ++i) {
          var node = nodes[i];
          if (kinds[node[0]]) {
            for (var slot = 1; slot <= kinds[node[0]].arity; ++slot) {
              if (is_external(links[i+":"+slot])) {
                cases += "      attach(mem, "+dest_code(i+":"+slot)+");\n";
              }
            }
          }
        }
        cases += "      return true;\n";
      }
    };
    for (var kind_name in kinds) {
      kinds[kinds[kind_name].kind] = kinds[kind_name];
    }

    var rewrite_source = [
      "(function rewrite(mem, a_dest, b_dest) {",
      "  var a_info, b_info, a_kind, b_kind;",
      "  var a_out2, a_out3, a_out4, a_out5, a_out6, a_out7, a_out8;",
      "  var b_out2, b_out3, b_out4, b_out5, b_out6, b_out7, b_out8;",
      "  var n0_dest, n1_dest, n2_dest, n3_dest, n4_dest, n5_dest, n6_dest, n7_dest;",
      "  a_info = mem.val[a_dest];",
      "  b_info = mem.val[b_dest];",
      "  a_kind = get_kind(a_info);",
      "  b_kind = get_kind(b_info);",
      "  // Performs reduction",
      "  switch (b_kind * "+rules.length+" + a_kind) {",
      cases,
      "  }",
      "  return false;",
      "})",
    ].join("\n");

    var rewrite = eval(rewrite_source);

    return {cases, kinds, rewrite_source, rewrite};
  };

  var {kinds, rewrite} = build_rules(rules);

  function Memory() {
    return {val: [], ant: [], len: 0};
  }

  function alloc(mem, size) {
    var ptr = mem.len;
    mem.len += size;
    return ptr;
  }

  function clear() {
    // TODO
  }

  function new_port(dest, slot) {
    return ((dest << 4) | slot) >>> 0;
  }

  function get_dest(port) {
    return port >>> 4;
  }

  function get_slot(port) {
    return port & 0xF;
  }

  // If port points to air, attach it to the next concrete node
  function attach(mem, port) {
    var next = mem.val[get_dest(port) + get_slot(port)];
    while (is_air(get_kind(mem.val[get_dest(next)]))) {
      next = mem.val[get_dest(next) + get_slot(next)];
    }
    //console.log("pointing", port, "to", next);
    mem.val[get_dest(port) + get_slot(port)] = next;
  }

  // PortIsNum:16 | Done:1 | Kind:15 | 
  function new_info(kind, done, port_is_num = 0) {
    return ((port_is_num << 16) | (done << 15) | kind) >>> 0;
  }

  function port_is_num(info) {
    return 0; // TODO
  }

  function is_done(info) {
    return (info >>> 15) & 1;
  }

  function set_done(info) {
    return (info | (1 << 15)) >>> 0;
  }

  function get_kind(info) {
    return info & 0x7FFF;
  }

  function is_air(kind) {
    return kind < 16;
  }

  function reduce_step(mem) {
    var new_ant = [];
    for (var ant = 0; ant < mem.ant.length; ++ant) {
      var prev = mem.ant[ant].pop();
      var next = mem.val[get_dest(prev) + get_slot(prev)];
      var info = mem.val[get_dest(next)];
      var kind = get_kind(info);
      // We're on air. Some ant reduced our node.
      if (is_air(kind)) {
        new_ant.push(mem.ant[ant]);
      // We're on a node.
      } else if (!is_done(info)) {
        // On main port
        if (get_slot(next) === 1) {
          var rewritten = false;
          // If active pair: perform rewrite, go back
          if (get_slot(prev) === 1) {
            if (rewrite(mem, get_dest(prev), get_dest(next))) {
              rewritten = true;
              new_ant.push(mem.ant[ant]);
            }
          }
          // If not active: mark node as done, go to its aux ports
          if (!rewritten) {
            var arity = kinds[kind].arity;
            mem.val[get_dest(next)] = set_done(info);
            for (var slot = 2; slot <= arity; ++slot) {
              new_ant.push([new_port(get_dest(next), slot)]);
            }
          }
        // On aux port: push slot to back-array, go to main port
        } else {
          mem.ant[ant].push(prev);
          mem.ant[ant].push(new_port(get_dest(next), 1));
          new_ant.push(mem.ant[ant]);
        }
      }
    }
    mem.ant = new_ant;
  }

  function read(code) {
    var mem = Memory();
    var vars = {};
    var lines = code.split("\n");
    for (var i = 0; i < lines.length; ++i) {
      if (lines[i] !== "") {
        var words = lines[i].split(" ").filter(x => x !== "");
        var name = words[0];
        var kind = kinds[name].kind;
        var ptr = alloc(mem, words.length);
        mem.val[ptr] = new_info(kind, 0);
        //console.log("->", name, kind, kinds);
        if (words.length - 1 !== kinds[kind].arity) {
          throw "Wrong arity on " + kind + ": " + (words.length - 1) + " instead of " + kinds[kind].arity + ".";
        }
        for (var j = 1; j <= kinds[kind].arity; ++j) {
          var dest = vars[words[j]];
          if (dest) {
            mem.val[get_dest(dest) + get_slot(dest)] = new_port(ptr, j);
            mem.val[ptr + j] = dest;
          } else {
            vars[words[j]] = new_port(ptr, j);
            mem.val[ptr + j] = new_port(ptr, j);
          }
        }
      }
    };
    return mem;
  }

  function show(mem) {
    function nth_name(n) {
      var str = "";
      ++n;
      while (n > 0) {
        --n;
        str += String.fromCharCode(97 + n % 26);
        n = Math.floor(n / 26);
      }
      return str;
    };
    function padr(len, str) {
      return str.length >= len ? str : padr(len, str + " ");
    }
    function padl(len, str) {
      return str.length >= len ? str : padl(len, " " + str);
    }
    var has_ant = {};
    for (var ant = 0; ant < mem.ant.length; ++ant) {
      var ant_port = mem.ant[ant].slice(-1)[0];
      has_ant[get_dest(ant_port)+":"+get_slot(ant_port)] = true;
    }
    var lines = [];
    var names = {};
    var count = 0;
    var dest = 0;
    while (dest < mem.val.length) {
      var info = mem.val[dest];
      var kind = get_kind(info);
      var {name, arity} = kinds[get_kind(info)];
      if (!is_air(kind)) {
        var line = padr(6, name);
        for (var slot = 1; slot <= arity; ++slot) {
          var self_port_key = dest+":"+slot;
          var dest_port_key = get_dest(mem.val[dest+slot])+":"+get_slot(mem.val[dest+slot]);
          var name = names[self_port_key] || nth_name(count++);
          var anty = has_ant[self_port_key] ? "*" : "";
          names[dest_port_key] = name;
          line = line + " " + padr(4, name.toUpperCase() + anty);
        }
        var done = is_done(info) ? "-" : " ";
        line = padl(4, String(dest)) + " |" + done + " " + line;
        lines.push(line);
      }
      dest = dest + 1 + arity;
    }
    return "-----,\n" + lines.join("\n") + "\n-----'";
  }

  return {
    build_rules,
    Memory,
    alloc,
    clear,
    new_port,
    get_dest,
    get_slot,
    attach,
    new_info,
    port_is_num,
    is_done,
    set_done,
    get_kind,
    is_air,
    reduce_step,
    read,
    show,
  };
};
