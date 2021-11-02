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
  function Memory() {
    return {
      val: [],
      ant: [],
      red: [],
      use: [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],
      len: 0,
      rwt: 0,
    };
  }

  function alloc(mem, size) {
    var reused = mem.use[size].pop();
    if (reused) {
      return reused;
    } else {
      var dest = mem.len;
      mem.len += size;
      return dest;
    }
  }

  function count_nodes(mem) {
    var count = 0;
    for (var dest = 0; dest < mem.val.length; dest = dest + arit + 1) {
      var kind = get_kind(mem.val[dest]);
      var arit = kinds[kind].arity;
      if (kind > 16) {
        ++count;
      }
    }
    return count;
  }

  function free(mem, dest, size) {
    mem.use[size].push(dest);
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
    var idx0 = (port >>> 4) + 1 + (port & 0xF);
    var next = mem.val[idx0];
    while ((mem.val[(next >>> 4)] & 0x7FFF) < 16) {
      next = mem.val[(next >>> 4) + 1 + (next & 0xF)];
    }
    mem.val[idx0] = next;
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

  function reduce_step_lazy(mem) {
    var new_ant = [];
    for (var ant = 0; ant < mem.ant.length; ++ant) {
      if (mem.ant[ant].length > 0) {
        var prev = mem.ant[ant].pop();
        var next = mem.val[get_dest(prev) + 1 + get_slot(prev)];
        var next_info = mem.val[get_dest(next)];
        var next_kind = get_kind(next_info);
        // We're on air. Some ant reduced our node.
        if (is_air(next_kind)) {
          new_ant.push(mem.ant[ant]);
        // We're on a node.
        } else if (!is_done(next_info)) {
          // On main port
          if (get_slot(next) === 0) {
            var rewritten = false;
            // If active pair: perform rewrite, go back
            if (get_slot(prev) === 0) {
              // Rewrites
              if (rewrite(mem, get_dest(prev), get_dest(next))) {
                rewritten = true;
                new_ant.push(mem.ant[ant]);
              }
            }
            // If not active: mark node as done, go to its aux ports
            if (!rewritten) {
              mem.val[get_dest(next)] = set_done(next_info);
              var next_arit = kinds[next_kind].arity;
              for (var slot = 1; slot < next_arit; ++slot) {
                new_ant.push([new_port(get_dest(next), slot)]);
              }
            }
          // On aux port: push slot to back-array, go to main port
          } else {
            mem.ant[ant].push(prev);
            mem.ant[ant].push(new_port(get_dest(next), 0));
            new_ant.push(mem.ant[ant]);
          }
        }
      }
    }
    mem.ant = new_ant;
  }
  
  function reduce_step(mem) {
    var red = mem.red;
    mem.red = [];
    for (var r = 0; r < red.length; ++r) {
      var a_dest = red[r];
      var a_out0 = mem.val[a_dest+1];
      var b_dest = get_dest(a_out0);
      var b_out0 = mem.val[b_dest+1];
      if (get_slot(a_out0) === 0 && get_slot(b_out0) === 0) {
        if (rewrite(mem, a_dest, b_dest)) {
          mem.rwt += 1;
        }
      }
    }
  }

  function find_redexes(mem) {
    mem.red = [];
    for (var dest = 0; dest < mem.val.length; dest = dest + arit + 1) {
      var arit = kinds[get_kind(mem.val[dest])].arity;
      check_redex(mem, dest);
    }
  }

  function check_redex(mem, dest) {
    var next = mem.val[dest+1];
    if (get_slot(next) === 0) {
      mem.red.push(dest);
    }
  }

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
      while (str !== "" && /[\w\-<>_]/.test(str[0])) {
        term += str[0];
        str = str.slice(1);
      }
      return [str, term];
    }
  };

  function show_sexp(sexp) {
    if (typeof sexp === "string") {
      return sexp;
    } else {
      return "("+sexp.map(show_sexp).join(" ")+")";
    }
  };

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
        if (words.length !== kinds[kind].arity + 1) {
          throw "Wrong arity on " + kind + ": " + (words.length - 1) + " instead of " + kinds[kind].arity + ".";
        }
        for (var j = 0; j < kinds[kind].arity; ++j) {
          var dest = vars[words[j+1]];
          //console.log(i,j,JSON.stringify(vars));
          if (dest !== undefined) {
            mem.val[get_dest(dest)+1+get_slot(dest)] = new_port(ptr, j);
            mem.val[ptr+1+j] = dest;
          } else {
            vars[words[j+1]] = new_port(ptr, j);
            mem.val[ptr+1+j] = new_port(ptr, j);
          }
        }
      }
    };
    find_redexes(mem);
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
      //console.log(mem);
      //console.log("->", info, get_kind(info));
      var {name, arity} = kinds[get_kind(info)];
      if (!is_air(kind)) {
        var line = padr(5, name);
        for (var slot = 0; slot < arity; ++slot) {
          var self_port_key = dest+":"+slot;
          var dest_port_key = get_dest(mem.val[dest+1+slot])+":"+get_slot(mem.val[dest+1+slot]);
          if (self_port_key === dest_port_key) {
            var name = "@";
          } else {
            var name = names[self_port_key] || nth_name(count++);
          }
          var anty = has_ant[self_port_key] ? "*" : "";
          names[dest_port_key] = name;
          //var name = name + "-" + new_port(dest,slot);
          line = line + " " + padr(4, name.toUpperCase() + anty);
        }
        var done = is_done(info) ? "-" : " ";
        line = padl(4, String(dest)) + " |" + done + " " + line;
        line = (mem.red.indexOf(dest) !== -1 ? "#" : "|") + line;
        lines.push(line);
      }
      dest = dest + 1 + arity;
    }
    return "-----,\n" + lines.join("\n") + "\n-----'";
  }

  function show_tree(mem, port = null) {
    port = port || mem.val[1];
    var info = mem.val[get_dest(port)];
    var kind = get_kind(info);
    if (kinds[kind].arity <= 1) {
      return "(" + kinds[kind].name + ")";
    } else {
      var text = kinds[kind].name;
      if (kinds[kind].is_ctor) {
        for (var i = 1; i < kinds[kind].arity; ++i) {
          text += " " + show_tree(mem, mem.val[get_dest(port)+1+i]);
        }
      } else {
        for (var i = 0; i < kinds[kind].arity - 1; ++i) {
          text += " " + show_tree(mem, mem.val[get_dest(port)+1+i]);
        }
      }
      return "(" + text + ")";
    }
  }

  function read_tree(code) {
    var nodes = [];
    var count = 0;
    function go(up, expr) {
      var node = [expr[0]];
      //console.log(expr[0], kinds);
      if (kinds[expr[0]].is_ctor) {
        node.push(up);
        for (var i = 1; i < expr.length; ++i) {
          node.push(go("$"+(count++), expr[i]));
        }
      } else {
        for (var i = 1; i < expr.length; ++i) {
          node.push(go("$"+(count++), expr[i]));
        }
        node.push(up);
      }
      nodes.push(node);
      return up;
    }
    go("R", parse_sexp(code)[1]);
    var nodes = [["Rot","R"]].concat(nodes.reverse());
    var ncode = nodes.map(x => x.join(" ")).join("\n");
    //console.log(ncode);
    return read(ncode);
  }

  function build_rules(code) {

    function is_external(var_name) {
      return var_name[0] === "<" || var_name[0] === ">";
    }

    function dest_code(dest) {
      if (is_external(dest)) {
        return dest[0] === "<" ? "a_out"+Number(dest[1]) : "b_out"+Number(dest[1]);
      } else {
        var [i,slot] = dest.split(":");
        return port_code("n"+i+"_dest", slot);
      }
    }

    function port_code(dest, slot) {
      return "((("+dest+" << 4) | "+slot+") >>> 0)";
    }

    function info_code(kind) {
      return kind;
    }

    function case_to_rules(equat) {
      var rules = [];
      var arity = {};
      //console.log(JSON.stringify(equat));
      var vars = [];
      var func = equat[0];
      var call = func;
      // For each argument of the equation...
      for (var arg = 1; arg < equat.length - 1; ++arg) {
        var ctor = equat[arg];
        // Check if this is the last deconstructed argument
        var is_last_elim = true;
        for (var k = arg + 1; k < equat.length - 1; ++k) {
          if (typeof equat[k] !== "string") {
            is_last_elim = false;
          }
        }
        // If this is a deconstructed argument...
        if (!is_last_elim) {
          var done = [func+"_"+ctor[0]];
          // Moves function wires 1 slot left
          for (var i = 0; i < kinds[func].arity-1; ++i) {
            done.push("<"+(i+1));
          }
          // Append ctor variables to the end
          for (var i = 0; i < kinds[ctor[0]].arity-1; ++i) { 
            done.push(">"+(i+1));
            vars.push(ctor[i+1]);
          }
          // Registers the rule
          rules.push(["rule",call,ctor[0],done]);
          // Updates the call name
          call = call + "_" + ctor[0];
          //console.log("---", show_sexp(rule));
        // If this is the right-hand side (i.e., returned body)
        } else {
          // Converts the returned tree into separate nodes and names variables
          function make_return(up_link, expr, var_name) {
            if (typeof expr === "string") {
              return [[var_name[expr] || expr, up_link]];
            } else {
              var result = [];
              var count = 0;
              function go(up_link, expr) {
                if (typeof expr === "string") {
                  return var_name[expr] || expr;
                } else {
                  var node = [expr[0]];
                  if (kinds[expr[0]].is_ctor) {
                    node.push(up_link);
                  }
                  for (var i = 1; i < expr.length; ++i) {
                    var down_link = "$"+(count++);
                    node.push(go(down_link, expr[i]));
                  }
                  if (!kinds[expr[0]].is_ctor) {
                    node.push(up_link);
                  }
                  result.push(node);
                  return up_link;
                }
              }
              go(up_link, expr);
              return result;
            }
          }
          arity[call] = kinds[func].arity - arg + 1 + vars.length;
          var var_name = {};
          // Registers fields of last matched ctor
          for (var i = 0; i < kinds[ctor[0]].arity-1; ++i) {
            var_name[ctor[i+1]] = ">" + (i + 1);
          }
          // Registers unmatched arguments
          for (var i = 0; i < equat.length - arg - 2; ++i) {
            var_name[equat[arg + i + 1]] = "<" + (i + 1);
          }
          // Registers fields from previous matched ctors
          for (var i = 0; i < vars.length; ++i) {
            var_name[vars[i]] = "<" + (kinds[func].arity-1 - (arg - 1) + i + 1);
          }
          // Registers the rule
          var uptr = "<"+(kinds[func].arity-1-(arg-1));
          var body = equat[equat.length-1];
          var nods = make_return(uptr,body,var_name);
          rules.push(["rule",call,ctor[0]].concat(nods));
          //console.log("===", show_sexp(rule), vars, JSON.stringify(var_name), "arg:"+arg, "ret:"+ret);
          break;
        }
      }
      return {rules, arity};
    }

    var [code_rest, statements] = parse_sexp("("+code+")");

    var kinds = {
      Air0: {name: "Air0", arity: 0, kind: 0, is_ctor: false},
      Air1: {name: "Air1", arity: 1, kind: 1, is_ctor: false},
      Air2: {name: "Air2", arity: 2, kind: 2, is_ctor: false},
      Air3: {name: "Air3", arity: 3, kind: 3, is_ctor: false},
      Air4: {name: "Air4", arity: 4, kind: 4, is_ctor: false},
      Air5: {name: "Air5", arity: 5, kind: 5, is_ctor: false},
      Air6: {name: "Air6", arity: 6, kind: 6, is_ctor: false},
      Air7: {name: "Air7", arity: 7, kind: 7, is_ctor: false},
      Air8: {name: "Air8", arity: 8, kind: 8, is_ctor: false},
      Air9: {name: "Air9", arity: 9, kind: 9, is_ctor: false},
      Air10: {name: "Air10", arity: 10, kind: 10, is_ctor: false},
      Air11: {name: "Air11", arity: 11, kind: 11, is_ctor: false},
      Air12: {name: "Air12", arity: 12, kind: 12, is_ctor: false},
      Air13: {name: "Air13", arity: 13, kind: 13, is_ctor: false},
      Air14: {name: "Air14", arity: 14, kind: 14, is_ctor: false},
      Air15: {name: "Air15", arity: 15, kind: 15, is_ctor: false},
      Rot: {name: "Rot", arity: 1, kind: 16, is_ctor: false},
      Era: {name: "Era", arity: 1, kind: 17, is_ctor: false},
    };

    var rules = [];

    var total_kinds = Object.keys(kinds).length;

    for (var statement of statements) {
      switch (statement[0]) {
        case "node":
          var name = statement[1];
          var arity = Number(statement[2]);
          kinds[name] = {name, arity, is_ctor: false, kind: Object.keys(kinds).length};
          total_kinds++;
          break;
        case "func":
          var name = statement[1];
          var arity = Number(statement[2]) + 1;
          kinds[name] = {name, arity, is_ctor: false, kind: Object.keys(kinds).length};
          total_kinds++;
          break;
        case "ctor":
          var name = statement[1];
          var arity = Number(statement[2]) + 1;
          kinds[name] = {name, arity, is_ctor: true, kind: Object.keys(kinds).length};
          total_kinds++;
          break;
        case "rule":
          rules.push(statement);
          break;
        case "case":
          var {rules: new_rules, arity: new_arity} = case_to_rules(statement[1].concat([statement[2]]));
          for (var new_rule of new_rules) {
            //console.log("pushing", show_sexp(new_rule));
            rules.push(new_rule);
          }
          for (var new_rule_name in new_arity) {
            if (!kinds[new_rule_name]) {
              kinds[new_rule_name] = {
                name: new_rule_name,
                arity: new_arity[new_rule_name],
                is_ctor: false,
                kind: Object.keys(kinds).length,
              }
            }
          }
          break;
        default:
          throw "Unknown statement: " + kinds[0];
      }
    }

    // Removes duplicate rules
    var unique_rules = [];
    var repeated = {};
    for (var i = rules.length - 1; i >= 0; --i) {
      var key = rules[i][1]+"-"+rules[i][2];
      if (!repeated[key]) {
        unique_rules.push(rules[i]);
      }
      repeated[key] = true;
    }
    rules = unique_rules.reverse();

    // Builds the erasure code for each kind
    var erasures = "";
    for (var k in kinds) {
      var a_kind = kinds[k];
      if (a_kind.kind >= 18) {
        erasures += "      case "+a_kind.kind+": // --" + a_kind.name+";\n";
        //erasures += "        console.log('--"+a_kind.name+"',a_dest);\n";
        erasures += "        // gets neighbors\n";
        for (var i = 1; i < a_kind.arity; ++i) {
          erasures += "        a_out"+i+" = mem.val[a_dest+1+"+i+"];\n";
        }
        erasures += "        // turns old node into air\n";
        erasures += "        mem.val[a_dest] = "+info_code(a_kind.arity)+";\n";
        erasures += "        // attaches eraser to neighbor ports\n";
        for (var i = 1; i < a_kind.arity; ++i) {
          erasures += "        mem.val[get_dest(a_out"+i+")+1+get_slot(a_out"+i+")] = a_out"+i+";\n";
        }
        //erasures += "        // creates new ants\n";
        //for (var i = 1; i < a_kind.arity; ++i) {
          //erasures += "        new_ant.push([a_out"+i+"]);\n";
        //}
        erasures += "        // checks external ports for redexes\n";
        for (var i = 1; i < a_kind.arity; ++i) {
          erasures += "        check_redex(mem, get_dest(a_out"+i+"));\n";
        }
        erasures += "        // frees memory used by node\n";
        erasures += "        free(mem, a_dest, "+(a_kind.arity+1)+");\n";
        erasures += "        return true;\n";
      }
    }

    // Builds the case code for each rule on the rule table
    var cases = "";

    for (var rule of rules) {
      // Gets active pair kinds (ex: `{name: 'Add', arity: 3, kind: 4}`)
      var a_name = rule[1];
      var b_name = rule[2];
      var nodes  = rule.slice(3);
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
          var vars = node.slice(1);
          for (var i_slot = 0; i_slot < vars.length; ++i_slot) {
            if (is_external(vars[i_slot])) { // external connection
              links[vars[i_slot]] = i+":"+i_slot;
              links[i+":"+i_slot] = vars[i_slot];
            } else { // internal connection
              if (!links[vars[i_slot]]) {
                links[vars[i_slot]] = i+":"+i_slot;
              } else {
                var [j,j_slot] = links[vars[i_slot]].split(":").map(Number);
                delete links[vars[i_slot]];
                links[i+":"+i_slot] = j+":"+j_slot;
                links[j+":"+j_slot] = i+":"+i_slot;
              }
            }
          }
        } else {
          links[node[0]] = node[1];
          links[node[1]] = node[0];
        }
      }

      // Links unused ports to themselves, triggering erasure
      for (var i = 1; i < a_kind.arity; ++i) {
        if (!links["<"+i]) links["<"+i] = "<"+i;
      }
      for (var i = 1; i < b_kind.arity; ++i) {
        if (!links[">"+i]) links[">"+i] = ">"+i;
      }

      //console.log("LINKS", links);
      //process.exit();
      //console.log(kinds);

      // Builds the case code
      //console.log(a_kind, b_kind);
      if (a_kind.kind !== b_kind.kind) {
        cases += "      case "+(a_kind.kind * total_kinds + b_kind.kind)+": // " + b_kind.name+"-"+a_kind.name+";\n";
        cases += "        return rewrite(mem, b_dest, a_dest);\n";
      }
      cases += "      case "+(b_kind.kind * total_kinds + a_kind.kind)+": // " + a_kind.name+"-"+b_kind.name+";\n";
      //cases += "        console.log('"+a_kind.name+"-"+b_kind.name+"');\n";
      cases += "        // gets neighbors\n";
      for (var i = 1; i < a_kind.arity; ++i) {
        cases += "        a_out"+i+" = mem.val[a_dest+1+"+i+"];\n"
      }
      for (var i = 1; i < b_kind.arity; ++i) {
        cases += "        b_out"+i+" = mem.val[b_dest+1+"+i+"];\n"
      }
      cases += "        // allocs new nodes\n";
      for (var i = 0; i < nodes.length; ++i) {
        var node = nodes[i];
        if (kinds[node[0]]) {
          cases += "        n"+i+"_dest = alloc(mem,"+(kinds[node[0]].arity+1)+");\n";
        }
      }
      cases += "        // fills new nodes\n";
      for (var i = 0; i < nodes.length; ++i) {
        var new_node = nodes[i];
        var new_kind = kinds[new_node[0]];
        if (new_kind) {
          cases += "        mem.val[n"+i+"_dest] = "+info_code(new_kind.kind)+";\n";
          for (var slot = 0; slot < new_kind.arity; ++slot) {
            var var_name = new_node[slot];
            //console.log(a_kind.name, b_kind.name, i+":"+slot, links[i+":"+slot])
            cases += "        mem.val[n"+i+"_dest+1+"+slot+"] = "+dest_code(links[i+":"+slot])+";\n";
          }
        }
      }
      cases += "        // turns old nodes into air\n";
      cases += "        mem.val[a_dest] = "+info_code(a_kind.arity)+";\n";
      cases += "        mem.val[b_dest] = "+info_code(b_kind.arity)+";\n";
      cases += "        // points air ports to new destinations\n";
      for (var slot = 1; slot < a_kind.arity; ++slot) {
        cases += "        mem.val[a_dest+1+"+slot+"] = "+dest_code(links["<"+slot])+";\n";
      }
      for (var slot = 1; slot < b_kind.arity; ++slot) {
        cases += "        mem.val[b_dest+1+"+slot+"] = "+dest_code(links[">"+slot])+";\n";
      }
      cases += "        // attaches external ports\n";
      for (var slot = 1; slot < a_kind.arity; ++slot) {
        cases += "        attach(mem, a_out"+slot+");\n";
      }
      for (var slot = 1; slot < b_kind.arity; ++slot) {
        cases += "        attach(mem, b_out"+slot+");\n";
      }
      cases += "        // attaches internal ports that must point to external ports\n";
      for (var i = 0; i < nodes.length; ++i) {
        var node = nodes[i];
        if (kinds[node[0]]) {
          for (var slot = 0; slot < kinds[node[0]].arity; ++slot) {
            if (is_external(links[i+":"+slot])) {
              cases += "        attach(mem, "+dest_code(i+":"+slot)+");\n";
            }
          }
        }
      }
      cases += "        // checks new nodes for redexes\n";
      for (var i = 0; i < nodes.length; ++i) {
        if (kinds[node[0]]) {
          cases += "        check_redex(mem, n"+i+"_dest);\n";
        }
      }
      cases += "        // checks external ports for redexes\n";
      for (var slot = 1; slot < a_kind.arity; ++slot) {
        cases += "        check_redex(mem, get_dest(a_out"+slot+"));\n";
      }
      for (var slot = 1; slot < b_kind.arity; ++slot) {
        cases += "        check_redex(mem, get_dest(b_out"+slot+"));\n";
      }
      cases += "        free(mem, a_dest, "+(a_kind.arity+1)+");\n";
      cases += "        free(mem, b_dest, "+(b_kind.arity+1)+");\n";
      cases += "        return true;\n";
    }

    // Completes the kinds object
    for (var kind_name in kinds) {
      kinds[kinds[kind_name].kind] = kinds[kind_name];
    }

    var rewrite_source = [
      "(function rewrite(mem, a_dest, b_dest) {",
      "  var a_info, b_info, a_kind, b_kind;",
      "  var a_out1, a_out2, a_out3, a_out4, a_out5, a_out6, a_out7, a_out8;",
      "  var a_out1, b_out2, b_out3, b_out4, b_out5, b_out6, b_out7, b_out8;",
      "  var n0_dest, n1_dest, n2_dest, n3_dest, n4_dest, n5_dest, n6_dest, n7_dest;",
      "  a_info = mem.val[a_dest];",
      "  b_info = mem.val[b_dest];",
      "  a_kind = get_kind(a_info);",
      "  b_kind = get_kind(b_info);",
      "  // Performs erasure",
      "  if (a_dest === b_dest) {",
      "    switch (a_kind) {",
      erasures,
      "    }",
      "  } else {",
      "    // Performs reduction",
      "    switch (b_kind * "+total_kinds+" + a_kind) {",
      cases,
      "    }",
      "  }",
      "  return false;",
      "})",
    ].join("\n");

    
    console.log(rewrite_source);
    console.log(kinds);
    var rewrite = eval(rewrite_source);
    //console.log(rewrite);
    //process.exit();

    return {cases, kinds, rewrite_source, rewrite};
  };

  //var {kinds, rewrite} = build_rules(rules);

  global.stats = {};
  function register(str) {
    if (!global.stats[str]) {
      global.stats[str] = 0;
    }
    global.stats[str]++;
  }
  function rewrite(mem, a_dest, b_dest) {
    var a_info, b_info, a_kind, b_kind;
    var a_out1, a_out2, a_out3, a_out4, a_out5, a_out6, a_out7, a_out8;
    var a_out1, b_out2, b_out3, b_out4, b_out5, b_out6, b_out7, b_out8;
    var n0_dest, n1_dest, n2_dest, n3_dest, n4_dest, n5_dest, n6_dest, n7_dest;
    a_info = mem.val[a_dest];
    b_info = mem.val[b_dest];
    a_kind = a_info & 0x7FFF;
    b_kind = b_info & 0x7FFF;
    // Performs erasure
    if (a_dest === b_dest) {
      switch (a_kind) {
        case 18: // --O;
          //register("--O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // turns old node into air
          mem.val[a_dest] = 2;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          // frees memory used by node
          free(mem, a_dest, 3);
          return true;
        case 19: // --I;
          //register("--I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // turns old node into air
          mem.val[a_dest] = 2;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          // frees memory used by node
          free(mem, a_dest, 3);
          return true;
        case 20: // --E;
          //register("--E");
          // gets neighbors
          // turns old node into air
          mem.val[a_dest] = 1;
          // attaches eraser to neighbor ports
          // checks external ports for redexes
          // frees memory used by node
          free(mem, a_dest, 2);
          return true;
        case 21: // --Inc;
          //register("--I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // turns old node into air
          mem.val[a_dest] = 2;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          // frees memory used by node
          free(mem, a_dest, 3);
          return true;
        case 22: // --Rev;
          //register("--R");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          // turns old node into air
          mem.val[a_dest] = 3;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          mem.val[(a_out2>>>4)+1+(a_out2&0xF)] = a_out2;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          // frees memory used by node
          free(mem, a_dest, 4);
          return true;
        case 23: // --Fn0;
          //register("--F");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // turns old node into air
          mem.val[a_dest] = 2;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          // frees memory used by node
          free(mem, a_dest, 3);
          return true;
        case 24: // --Fn1;
          //register("--F");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          a_out3 = mem.val[a_dest+1+3];
          // turns old node into air
          mem.val[a_dest] = 4;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          mem.val[(a_out2>>>4)+1+(a_out2&0xF)] = a_out2;
          mem.val[(a_out3>>>4)+1+(a_out3&0xF)] = a_out3;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (a_out3>>>4));
          // frees memory used by node
          free(mem, a_dest, 5);
          return true;
        case 25: // --Fn2;
          //register("--F");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          // turns old node into air
          mem.val[a_dest] = 3;
          // attaches eraser to neighbor ports
          mem.val[(a_out1>>>4)+1+(a_out1&0xF)] = a_out1;
          mem.val[(a_out2>>>4)+1+(a_out2&0xF)] = a_out2;
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          // frees memory used by node
          free(mem, a_dest, 4);
          return true;
      }
    } else {
      // Performs reduction
      switch (b_kind * 26 + a_kind) {
        case 566: // E-Inc;
          return rewrite(mem, b_dest, a_dest);
        case 541: // Inc-E;
          //register("Inc-E");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,2);
          // fills new nodes
          mem.val[n0_dest] = 20;
          mem.val[n0_dest+1+0] = a_out1;
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 1;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 0) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 2);
          return true;
        case 564: // O-Inc;
          return rewrite(mem, b_dest, a_dest);
        case 489: // Inc-O;
          //register("Inc-O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          // fills new nodes
          mem.val[n0_dest] = 19;
          mem.val[n0_dest+1+0] = a_out1;
          mem.val[n0_dest+1+1] = b_out1;
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[b_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 0) >>> 0));
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 3);
          return true;
        case 565: // I-Inc;
          return rewrite(mem, b_dest, a_dest);
        case 515: // Inc-I;
          //register("Inc-I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,3);
          // fills new nodes
          mem.val[n0_dest] = 21;
          mem.val[n0_dest+1+0] = b_out1;
          mem.val[n0_dest+1+1] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n1_dest] = 18;
          mem.val[n1_dest+1+0] = a_out1;
          mem.val[n1_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[b_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 0) >>> 0));
          attach(mem, (((n1_dest << 4) | 0) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 3);
          return true;
        case 592: // E-Rev;
          return rewrite(mem, b_dest, a_dest);
        case 542: // Rev-E;
          //register("Rev-E");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          // allocs new nodes
          // fills new nodes
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 1;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = a_out2;
          mem.val[a_dest+1+2] = a_out1;
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          // attaches internal ports that must point to external ports
          // checks new nodes for redexes
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 2);
          return true;
        case 590: // O-Rev;
          return rewrite(mem, b_dest, a_dest);
        case 490: // Rev-O;
          //register("Rev-O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,4);
          // fills new nodes
          mem.val[n0_dest] = 18;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n0_dest+1+1] = a_out1;
          mem.val[n1_dest] = 22;
          mem.val[n1_dest+1+0] = b_out1;
          mem.val[n1_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+2] = a_out2;
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+2] = (((n1_dest << 4) | 2) >>> 0);
          mem.val[b_dest+1+1] = (((n1_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n1_dest << 4) | 0) >>> 0));
          attach(mem, (((n1_dest << 4) | 2) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 3);
          return true;
        case 591: // I-Rev;
          return rewrite(mem, b_dest, a_dest);
        case 516: // Rev-I;
          //register("Rev-I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,4);
          // fills new nodes
          mem.val[n0_dest] = 19;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n0_dest+1+1] = a_out1;
          mem.val[n1_dest] = 22;
          mem.val[n1_dest+1+0] = b_out1;
          mem.val[n1_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+2] = a_out2;
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+2] = (((n1_dest << 4) | 2) >>> 0);
          mem.val[b_dest+1+1] = (((n1_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n1_dest << 4) | 0) >>> 0));
          attach(mem, (((n1_dest << 4) | 2) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 3);
          return true;
        case 618: // E-Fn0;
          return rewrite(mem, b_dest, a_dest);
        case 543: // Fn0-E;
          //register("Fn0-E");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,2);
          n1_dest = alloc(mem,3);
          n2_dest = alloc(mem,2);
          n3_dest = alloc(mem,2);
          n4_dest = alloc(mem,5);
          // fills new nodes
          mem.val[n0_dest] = 20;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[n1_dest] = 21;
          mem.val[n1_dest+1+0] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+1] = (((n4_dest << 4) | 0) >>> 0);
          mem.val[n2_dest] = 20;
          mem.val[n2_dest+1+0] = (((n4_dest << 4) | 1) >>> 0);
          mem.val[n3_dest] = 20;
          mem.val[n3_dest+1+0] = (((n4_dest << 4) | 2) >>> 0);
          mem.val[n4_dest] = 24;
          mem.val[n4_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n4_dest+1+1] = (((n2_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+2] = (((n3_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+3] = a_out1;
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 1;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n4_dest << 4) | 3) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n4_dest << 4) | 3) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          check_redex(mem, n3_dest);
          check_redex(mem, n4_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 2);
          return true;
        case 616: // O-Fn0;
          return rewrite(mem, b_dest, a_dest);
        case 491: // Fn0-O;
          //register("Fn0-O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,3);
          n2_dest = alloc(mem,2);
          n3_dest = alloc(mem,2);
          n4_dest = alloc(mem,5);
          // fills new nodes
          mem.val[n0_dest] = 18;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[n0_dest+1+1] = b_out1;
          mem.val[n1_dest] = 21;
          mem.val[n1_dest+1+0] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+1] = (((n4_dest << 4) | 0) >>> 0);
          mem.val[n2_dest] = 20;
          mem.val[n2_dest+1+0] = (((n4_dest << 4) | 1) >>> 0);
          mem.val[n3_dest] = 20;
          mem.val[n3_dest+1+0] = (((n4_dest << 4) | 2) >>> 0);
          mem.val[n4_dest] = 24;
          mem.val[n4_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n4_dest+1+1] = (((n2_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+2] = (((n3_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+3] = a_out1;
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n4_dest << 4) | 3) >>> 0);
          mem.val[b_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n4_dest << 4) | 3) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          check_redex(mem, n3_dest);
          check_redex(mem, n4_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 3);
          return true;
        case 617: // I-Fn0;
          return rewrite(mem, b_dest, a_dest);
        case 517: // Fn0-I;
          //register("Fn0-I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,3);
          n2_dest = alloc(mem,2);
          n3_dest = alloc(mem,2);
          n4_dest = alloc(mem,5);
          // fills new nodes
          mem.val[n0_dest] = 19;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[n0_dest+1+1] = b_out1;
          mem.val[n1_dest] = 21;
          mem.val[n1_dest+1+0] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+1] = (((n4_dest << 4) | 0) >>> 0);
          mem.val[n2_dest] = 20;
          mem.val[n2_dest+1+0] = (((n4_dest << 4) | 1) >>> 0);
          mem.val[n3_dest] = 20;
          mem.val[n3_dest+1+0] = (((n4_dest << 4) | 2) >>> 0);
          mem.val[n4_dest] = 24;
          mem.val[n4_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n4_dest+1+1] = (((n2_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+2] = (((n3_dest << 4) | 0) >>> 0);
          mem.val[n4_dest+1+3] = a_out1;
          // turns old nodes into air
          mem.val[a_dest] = 2;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n4_dest << 4) | 3) >>> 0);
          mem.val[b_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n4_dest << 4) | 3) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          check_redex(mem, n3_dest);
          check_redex(mem, n4_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 3);
          free(mem, b_dest, 3);
          return true;
        case 644: // E-Fn1;
          return rewrite(mem, b_dest, a_dest);
        case 544: // Fn1-E;
          //register("Fn1-E");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          a_out3 = mem.val[a_dest+1+3];
          // allocs new nodes
          n0_dest = alloc(mem,4);
          // fills new nodes
          mem.val[n0_dest] = 25;
          mem.val[n0_dest+1+0] = a_out1;
          mem.val[n0_dest+1+1] = a_out2;
          mem.val[n0_dest+1+2] = a_out3;
          // turns old nodes into air
          mem.val[a_dest] = 4;
          mem.val[b_dest] = 1;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[a_dest+1+2] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+3] = (((n0_dest << 4) | 2) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, a_out3);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 0) >>> 0));
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n0_dest << 4) | 2) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (a_out3>>>4));
          free(mem, a_dest, 5);
          free(mem, b_dest, 2);
          return true;
        case 642: // O-Fn1;
          return rewrite(mem, b_dest, a_dest);
        case 492: // Fn1-O;
          //register("Fn1-O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          a_out3 = mem.val[a_dest+1+3];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,3);
          n2_dest = alloc(mem,5);
          // fills new nodes
          mem.val[n0_dest] = 18;
          mem.val[n0_dest+1+0] = (((n2_dest << 4) | 1) >>> 0);
          mem.val[n0_dest+1+1] = a_out1;
          mem.val[n1_dest] = 18;
          mem.val[n1_dest+1+0] = (((n2_dest << 4) | 2) >>> 0);
          mem.val[n1_dest+1+1] = a_out2;
          mem.val[n2_dest] = 24;
          mem.val[n2_dest+1+0] = b_out1;
          mem.val[n2_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n2_dest+1+2] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[n2_dest+1+3] = a_out3;
          // turns old nodes into air
          mem.val[a_dest] = 4;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+2] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+3] = (((n2_dest << 4) | 3) >>> 0);
          mem.val[b_dest+1+1] = (((n2_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, a_out3);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n1_dest << 4) | 1) >>> 0));
          attach(mem, (((n2_dest << 4) | 0) >>> 0));
          attach(mem, (((n2_dest << 4) | 3) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (a_out3>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 5);
          free(mem, b_dest, 3);
          return true;
        case 643: // I-Fn1;
          return rewrite(mem, b_dest, a_dest);
        case 518: // Fn1-I;
          //register("Fn1-I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          a_out3 = mem.val[a_dest+1+3];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,3);
          n1_dest = alloc(mem,3);
          n2_dest = alloc(mem,5);
          // fills new nodes
          mem.val[n0_dest] = 19;
          mem.val[n0_dest+1+0] = (((n2_dest << 4) | 1) >>> 0);
          mem.val[n0_dest+1+1] = a_out1;
          mem.val[n1_dest] = 19;
          mem.val[n1_dest+1+0] = (((n2_dest << 4) | 2) >>> 0);
          mem.val[n1_dest+1+1] = a_out2;
          mem.val[n2_dest] = 24;
          mem.val[n2_dest+1+0] = b_out1;
          mem.val[n2_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n2_dest+1+2] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[n2_dest+1+3] = a_out3;
          // turns old nodes into air
          mem.val[a_dest] = 4;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+2] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+3] = (((n2_dest << 4) | 3) >>> 0);
          mem.val[b_dest+1+1] = (((n2_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, a_out3);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n1_dest << 4) | 1) >>> 0));
          attach(mem, (((n2_dest << 4) | 0) >>> 0));
          attach(mem, (((n2_dest << 4) | 3) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (a_out3>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 5);
          free(mem, b_dest, 3);
          return true;
        case 670: // E-Fn2;
          return rewrite(mem, b_dest, a_dest);
        case 545: // Fn2-E;
          //register("Fn2-E");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          // allocs new nodes
          // fills new nodes
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 1;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = a_out2;
          mem.val[a_dest+1+2] = a_out1;
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          // attaches internal ports that must point to external ports
          // checks new nodes for redexes
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 2);
          return true;
        case 668: // O-Fn2;
          return rewrite(mem, b_dest, a_dest);
        case 493: // Fn2-O;
          //register("Fn2-O");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,2);
          n1_dest = alloc(mem,4);
          n2_dest = alloc(mem,3);
          // fills new nodes
          mem.val[n0_dest] = 20;
          mem.val[n0_dest+1+0] = (((n1_dest << 4) | 1) >>> 0);
          mem.val[n1_dest] = 22;
          mem.val[n1_dest+1+0] = a_out1;
          mem.val[n1_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          mem.val[n1_dest+1+2] = (((n2_dest << 4) | 0) >>> 0);
          mem.val[n2_dest] = 23;
          mem.val[n2_dest+1+0] = (((n1_dest << 4) | 2) >>> 0);
          mem.val[n2_dest+1+1] = a_out2;
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n1_dest << 4) | 0) >>> 0);
          mem.val[a_dest+1+2] = (((n2_dest << 4) | 1) >>> 0);
          mem.val[b_dest+1+1] = b_out1;
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n1_dest << 4) | 0) >>> 0));
          attach(mem, (((n2_dest << 4) | 1) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          check_redex(mem, n1_dest);
          check_redex(mem, n2_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 3);
          return true;
        case 669: // I-Fn2;
          return rewrite(mem, b_dest, a_dest);
        case 519: // Fn2-I;
          //register("Fn2-I");
          // gets neighbors
          a_out1 = mem.val[a_dest+1+1];
          a_out2 = mem.val[a_dest+1+2];
          b_out1 = mem.val[b_dest+1+1];
          // allocs new nodes
          n0_dest = alloc(mem,4);
          // fills new nodes
          mem.val[n0_dest] = 25;
          mem.val[n0_dest+1+0] = b_out1;
          mem.val[n0_dest+1+1] = a_out1;
          mem.val[n0_dest+1+2] = a_out2;
          // turns old nodes into air
          mem.val[a_dest] = 3;
          mem.val[b_dest] = 2;
          // points air ports to new destinations
          mem.val[a_dest+1+1] = (((n0_dest << 4) | 1) >>> 0);
          mem.val[a_dest+1+2] = (((n0_dest << 4) | 2) >>> 0);
          mem.val[b_dest+1+1] = (((n0_dest << 4) | 0) >>> 0);
          // attaches external ports
          attach(mem, a_out1);
          attach(mem, a_out2);
          attach(mem, b_out1);
          // attaches internal ports that must point to external ports
          attach(mem, (((n0_dest << 4) | 0) >>> 0));
          attach(mem, (((n0_dest << 4) | 1) >>> 0));
          attach(mem, (((n0_dest << 4) | 2) >>> 0));
          // checks new nodes for redexes
          check_redex(mem, n0_dest);
          // checks external ports for redexes
          check_redex(mem, (a_out1>>>4));
          check_redex(mem, (a_out2>>>4));
          check_redex(mem, (b_out1>>>4));
          free(mem, a_dest, 4);
          free(mem, b_dest, 3);
          return true;
      }
    }
    return false;
  }

  var kinds = {
    '0': { name: 'Air0', arity: 0, kind: 0, is_ctor: false },
    '1': { name: 'Air1', arity: 1, kind: 1, is_ctor: false },
    '2': { name: 'Air2', arity: 2, kind: 2, is_ctor: false },
    '3': { name: 'Air3', arity: 3, kind: 3, is_ctor: false },
    '4': { name: 'Air4', arity: 4, kind: 4, is_ctor: false },
    '5': { name: 'Air5', arity: 5, kind: 5, is_ctor: false },
    '6': { name: 'Air6', arity: 6, kind: 6, is_ctor: false },
    '7': { name: 'Air7', arity: 7, kind: 7, is_ctor: false },
    '8': { name: 'Air8', arity: 8, kind: 8, is_ctor: false },
    '9': { name: 'Air9', arity: 9, kind: 9, is_ctor: false },
    '10': { name: 'Air10', arity: 10, kind: 10, is_ctor: false },
    '11': { name: 'Air11', arity: 11, kind: 11, is_ctor: false },
    '12': { name: 'Air12', arity: 12, kind: 12, is_ctor: false },
    '13': { name: 'Air13', arity: 13, kind: 13, is_ctor: false },
    '14': { name: 'Air14', arity: 14, kind: 14, is_ctor: false },
    '15': { name: 'Air15', arity: 15, kind: 15, is_ctor: false },
    '16': { name: 'Rot', arity: 1, kind: 16, is_ctor: false },
    '17': { name: 'Era', arity: 1, kind: 17, is_ctor: false },
    '18': { name: 'O', arity: 2, is_ctor: true, kind: 18 },
    '19': { name: 'I', arity: 2, is_ctor: true, kind: 19 },
    '20': { name: 'E', arity: 1, is_ctor: true, kind: 20 },
    '21': { name: 'Inc', arity: 2, is_ctor: false, kind: 21 },
    '22': { name: 'Rev', arity: 3, is_ctor: false, kind: 22 },
    '23': { name: 'Fn0', arity: 2, is_ctor: false, kind: 23 },
    '24': { name: 'Fn1', arity: 4, is_ctor: false, kind: 24 },
    '25': { name: 'Fn2', arity: 3, is_ctor: false, kind: 25 },
    Air0: { name: 'Air0', arity: 0, kind: 0, is_ctor: false },
    Air1: { name: 'Air1', arity: 1, kind: 1, is_ctor: false },
    Air2: { name: 'Air2', arity: 2, kind: 2, is_ctor: false },
    Air3: { name: 'Air3', arity: 3, kind: 3, is_ctor: false },
    Air4: { name: 'Air4', arity: 4, kind: 4, is_ctor: false },
    Air5: { name: 'Air5', arity: 5, kind: 5, is_ctor: false },
    Air6: { name: 'Air6', arity: 6, kind: 6, is_ctor: false },
    Air7: { name: 'Air7', arity: 7, kind: 7, is_ctor: false },
    Air8: { name: 'Air8', arity: 8, kind: 8, is_ctor: false },
    Air9: { name: 'Air9', arity: 9, kind: 9, is_ctor: false },
    Air10: { name: 'Air10', arity: 10, kind: 10, is_ctor: false },
    Air11: { name: 'Air11', arity: 11, kind: 11, is_ctor: false },
    Air12: { name: 'Air12', arity: 12, kind: 12, is_ctor: false },
    Air13: { name: 'Air13', arity: 13, kind: 13, is_ctor: false },
    Air14: { name: 'Air14', arity: 14, kind: 14, is_ctor: false },
    Air15: { name: 'Air15', arity: 15, kind: 15, is_ctor: false },
    Rot: { name: 'Rot', arity: 1, kind: 16, is_ctor: false },
    Era: { name: 'Era', arity: 1, kind: 17, is_ctor: false },
    O: { name: 'O', arity: 2, is_ctor: true, kind: 18 },
    I: { name: 'I', arity: 2, is_ctor: true, kind: 19 },
    E: { name: 'E', arity: 1, is_ctor: true, kind: 20 },
    Inc: { name: 'Inc', arity: 2, is_ctor: false, kind: 21 },
    Rev: { name: 'Rev', arity: 3, is_ctor: false, kind: 22 },
    Fn0: { name: 'Fn0', arity: 2, is_ctor: false, kind: 23 },
    Fn1: { name: 'Fn1', arity: 4, is_ctor: false, kind: 24 },
    Fn2: { name: 'Fn2', arity: 3, is_ctor: false, kind: 25 }
  }

  return {
    build_rules,
    Memory,
    alloc,
    free,
    new_port,
    get_dest,
    get_slot,
    attach,
    new_info,
    port_is_num,
    find_redexes,
    is_done,
    set_done,
    get_kind,
    is_air,
    rewrite,
    reduce_step,
    read,
    show,
    show_tree,
    read_tree,
  };
};
