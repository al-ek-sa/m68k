const BITS = { ".b": 8, ".l": 32 };
const u32 = v => v >>> 0;

function alu(op, a, b, size) {
  const n = BITS[size], mod = 2 ** n, top = mod / 2;
  const x = u32(a) % mod, y = u32(b) % mod;
  const neg = v => v >= top;
  const big = f => Number(f(BigInt(x), BigInt(y)) % BigInt(mod));
  const bit = (v, k) => Math.floor(v / 2 ** k) % 2;
  const sub = (p, q) => {
    const r = (p - q + mod) % mod;
    return [r, +(neg(p) !== neg(q) && neg(r) !== neg(p)), +(p < q)];
  };
  const table = {
    PASS: () => [x, 0, 0],
    ZERO: () => [0, 0, 0],
    ADD: () => {
      const r = (x + y) % mod;
      return [r, +(neg(x) === neg(y) && neg(r) !== neg(x)), +(x + y >= mod)];
    },
    SUB: () => sub(x, y),
    NEG: () => sub(0, x),
    AND: () => [big((p, q) => p & q), 0, 0],
    OR: () => [big((p, q) => p | q), 0, 0],
    XOR: () => [big((p, q) => p ^ q), 0, 0],
    NOT: () => [mod - 1 - x, 0, 0],
    MUL: () => [big((p, q) => p * q), 0, 0],
    DIV: () => [Math.floor(x / y), 0, 0],
    ASL: () => [y >= n ? 0 : big((p, q) => p << q), 0, y === 0 || y > n ? 0 : bit(x, n - y)],
    LSL: () => table.ASL(),
    LSR: () => [y >= n ? 0 : Math.floor(x / 2 ** y), 0, y === 0 || y > n ? 0 : bit(x, y - 1)],
    ASR: () => [
      y >= n ? (neg(x) ? mod - 1 : 0) : (Math.floor((neg(x) ? x - mod : x) / 2 ** y) + mod) % mod,
      0,
      y === 0 ? 0 : bit(x, Math.min(y, n) - 1)
    ]
  };
  const [r, v, c] = table[op]();
  return { r, sr: `${+neg(r)}${+(r === 0)}${v}${c}` };
}

function merge(old, r, size) {
  return size === ".b" ? u32(old) - (u32(old) % 256) + r : r;
}

const opName = (op, size) => op + (size === ".b" ? ".B" : "");
const done = { jump: "next", jumpText: "next → fetch0" };

function fetch(ir, opcode, pc = 0x100) {
  return [
    {
      mu: "fetch0", jump: "+1", rtl: "MAR ← PC",
      sig: ["sel_mar=PC", "latch_mar"],
      flow: [[["PC", "MUX_MAR", "MAR"]]],
      set: { MAR: pc }
    },
    {
      mu: "fetch1", jump: "+1", rtl: "MDR ← mem[MAR]",
      sig: ["ram_rd", "mem_size=.w", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr"],
      flow: [[["MAR", "RAM"], ["MAR", "CMP"]], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"]]],
      set: { MDR: opcode }
    },
    {
      mu: "fetch2", jump: "map", jumpText: "map → μ-программа по опкоду", rtl: "IR ← MDR ; PC ← PC + 2",
      sig: ["latch_ir", "pc_inc=2", "sel_pc=PC+n", "latch_pc"],
      flow: [[["MDR", "IR"], ["PC", "ADD", "MUX_PC", "PC"]]],
      set: { IR: ir, PC: pc + 2 }
    }
  ];
}

function ext(mu, value, n, pcBefore) {
  const size = n === 4 ? ".l" : n === 2 ? ".w" : ".b";
  return [
    {
      mu: mu + "_e0", jump: "+1", rtl: "MAR ← PC",
      sig: ["sel_mar=PC", "latch_mar"],
      flow: [[["PC", "MUX_MAR", "MAR"]]],
      set: { MAR: pcBefore }
    },
    {
      mu: mu + "_e1", jump: "+1", rtl: "MDR ← mem[MAR] ; PC ← PC + " + n,
      sig: ["ram_rd", "mem_size=" + size, "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "pc_inc=" + n, "sel_pc=PC+n", "latch_pc"],
      flow: [[["MAR", "RAM"]], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["PC", "ADD", "MUX_PC", "PC"]]],
      set: { MDR: value, PC: pcBefore + n }
    }
  ];
}

const R1_SRC = ["IR", "J_S", "MUX_R1", "RF"];
const R1_DST = ["IR", "J_D1", "MUX_R1", "RF"];
const R1_SP = ["A7a", "MUX_R1", "RF"];
const R2_SRC = ["IR", "J_S2", "MUX_R2", "RF"];
const R2_DST = ["IR", "J_D2", "MUX_R2", "RF"];
const R2_IDX = ["IR", "MUX_R2", "RF"];
const WA_SRC = ["IR", "J_S2", "MUX_WR", "RF"];
const WA_DST = ["IR", "J_D2", "MUX_WR", "RF"];
const WA_SP = ["A7b", "MUX_WR", "RF"];
const R1 = { src: R1_SRC, dst: R1_DST, A7: R1_SP };
const WA = { src: WA_SRC, dst: WA_DST, A7: WA_SP };

function marFrom(mu, field, reg, value, jump) {
  return {
    mu, jump: jump || "+1", rtl: "MAR ← " + reg,
    sig: ["sel_r1=" + field, "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mar=ALU", "latch_mar"],
    flow: [[R1[field]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MAR", "MAR"]]],
    set: { MAR: value }
  };
}

function memRead(mu, value, size) {
  return {
    mu, jump: "+1", rtl: "MDR ← mem[MAR]",
    sig: ["ram_rd", "mem_size=" + size, "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr"],
    flow: [[["MAR", "RAM"], ["MAR", "CMP"]], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"]]],
    set: { MDR: value }
  };
}

function mdrToReg(mu, reg, old, size, note) {
  return (mdr) => {
    const { r, sr } = alu("PASS", mdr, 0, size);
    return {
      mu, ...done, rtl: reg + " ← MDR ; SR ← NZ, V = C = 0",
      sig: ["sel_alu_b=MDR", "alu_op=" + opName("PASS_B", size), "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=" + size, "latch_sr"],
      flow: [[["MDR", "MUX_B", "ALU"], WA_DST], [["ALU", "MUX_WB", "RF"], ["ALU", "SR"]]],
      set: { [reg]: merge(old, r, size), SR: sr },
      note
    };
  };
}

function regReg(o) {
  const size = o.size || ".l";
  const { r, sr } = alu(o.op, o.d1, o.d0, size);
  const value = merge(o.d1, r, size);
  return {
    name: o.name, group: o.group, about: o.about,
    init: { D0: o.d0, D1: o.d1 },
    steps: [
      ...fetch(o.name, o.opcode),
      {
        mu: o.mu, ...done, rtl: o.rtl,
        sig: ["sel_r1=dst", "sel_r2=src", "sel_alu_a=rdata1", "sel_alu_b=rdata2", "alu_op=" + opName(o.op, size), "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=" + size, "latch_sr"],
        flow: [[R1_DST, R2_SRC], [["RF", "MUX_A", "ALU"], ["RF", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]],
        set: { D1: value, SR: sr },
        note: o.note
      }
    ]
  };
}

function unary(o) {
  const size = o.size || ".l";
  const { r, sr } = alu(o.op, o.value, 0, size);
  const reads = o.op !== "ZERO";
  return {
    name: o.name, group: o.group, about: o.about,
    init: { [o.reg]: o.value },
    steps: [
      ...fetch(o.name, o.opcode),
      {
        mu: o.mu, ...done, rtl: o.rtl,
        sig: [...(reads ? ["sel_r1=dst", "sel_alu_a=rdata1"] : []), "alu_op=" + opName(o.op, size), "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=" + size, "latch_sr"],
        flow: reads
          ? [[R1_DST], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]]
          : [[WA_DST], [["ALU", "MUX_WB", "RF"], ["ALU", "SR"]]],
        set: { [o.reg]: merge(o.value, r, size), SR: sr },
        note: o.note
      }
    ]
  };
}

const LABEL = 0x180;

function brHead(name, opcode, m) {
  return [
    ...fetch(name, opcode),
    {
      mu: m + "0", jump: "+1", rtl: "MAR ← PC",
      sig: ["sel_mar=PC", "latch_mar"],
      flow: [[["PC", "MUX_MAR", "MAR"]]],
      set: { MAR: 0x102 }
    }
  ];
}

function brRead(mu, jump, jumpText, note) {
  return {
    mu, jump, jumpText, rtl: "MDR ← mem[MAR] ; PC ← PC + 4",
    sig: ["ram_rd", "mem_size=.l", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "pc_inc=4", "sel_pc=PC+n", "latch_pc"],
    flow: [[["MAR", "RAM"], ["SR", "st_sr"]], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["PC", "ADD", "MUX_PC", "PC"]]],
    set: { MDR: LABEL, PC: 0x106 },
    note
  };
}

function brCheck(mu, flag, value, jumpText, note) {
  return {
    mu, jump: "cond", jumpText, rtl: "проверка флага " + flag,
    sig: [],
    flow: [[["SR", "st_sr"]]],
    set: {}, label: flag + " = " + value,
    note
  };
}

function brTake(mu) {
  return {
    mu, ...done, rtl: "PC ← MDR",
    sig: ["sel_pc=MDR", "latch_pc"],
    flow: [[["MDR", "MUX_PC", "PC"]]],
    set: { PC: LABEL }
  };
}

const FLAG_POS = { N: 0, Z: 1, V: 2, C: 3 };

function branch1(name, opcode, flag, want, sr, about) {
  const m = name.split(" ")[0];
  const value = +sr[FLAG_POS[flag]];
  const taken = value === want;
  return {
    name, group: "Переходы", about, init: { SR: sr },
    steps: [
      ...brHead(name, opcode, m),
      brRead(m + "1", "cond", "if " + flag + " = " + (1 - want) + " → fetch0, иначе +1",
        taken ? flag + " = " + value + " — переход будет" : flag + " = " + value + " — перехода нет, PC уже на следующей команде"),
      ...(taken ? [brTake(m + "2")] : [])
    ]
  };
}

function branchN(name, opcode, sr, about, checks) {
  const m = name.split(" ")[0];
  const [first, ...rest] = checks;
  return {
    name, group: "Переходы", about, init: { SR: sr },
    steps: [
      ...brHead(name, opcode, m),
      brRead(m + "1", "cond", first.jt, first.note),
      ...rest.map(c => brCheck(c.mu, c.flag, +sr[FLAG_POS[c.flag]], c.jt, c.note)),
      brTake(m + "_t")
    ]
  };
}

const PROGRAMS = [
  {
    name: "move.l D0, D1", group: "Пересылка",
    about: "Копия регистра в регистр. Значение проходит через ALU операцией PASS_A, чтобы выставить флаги N и Z.",
    init: { D0: 42, D1: 0 },
    steps: [
      ...fetch("move.l D0, D1", 0x2200),
      {
        mu: "mvrr0", ...done, rtl: "D1 ← D0 ; SR ← NZ, V = C = 0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.l", "latch_sr"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]],
        set: { D1: 42, SR: alu("PASS", 42, 0, ".l").sr }
      }
    ]
  },
  {
    name: "move.l 42, D0", group: "Пересылка",
    about: "Непосредственный операнд лежит в команде сразу за опкодом: ещё два такта, чтобы его прочитать.",
    init: { D0: 0 },
    steps: [
      ...fetch("move.l 42, D0", 0x203c),
      ...ext("imm", 42, 4, 0x102),
      mdrToReg("imm0", "D0", 0, ".l")(42)
    ]
  },
  {
    name: "move.b D0, D1", group: "Пересылка",
    about: "Байтовая пересылка: в D1 меняется только младший байт, флаги считаются по биту 7.",
    init: { D0: 0x1f5, D1: 0x300 },
    steps: [
      ...fetch("move.b D0, D1", 0x1200),
      {
        mu: "mvb0", ...done, rtl: "D1[7:0] ← D0[7:0] ; SR ← NZ",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A.B", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.b", "latch_sr"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]],
        set: { D1: merge(0x300, 0xf5, ".b"), SR: alu("PASS", 0x1f5, 0, ".b").sr },
        note: "байт 0xF5 отрицательный: N = 1; старшие байты D1 не тронуты"
      }
    ]
  },
  {
    name: "move.l (A0)+, D1", group: "Пересылка",
    about: "Чтение по адресу из A0 и постинкремент A0 на 4, пока память занята чтением.",
    init: { A0: 0x200, D1: 0 },
    steps: [
      ...fetch("move.l (A0)+, D1", 0x2218),
      marFrom("mvpi0", "src", "A0", 0x200),
      {
        mu: "mvpi1", jump: "+1", rtl: "MDR ← mem[MAR] ; A0 ← A0 + 4",
        sig: ["ram_rd", "mem_size=.l", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "sel_r1=src", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=ADD", "sel_wa=src", "sel_wb=ALU", "reg_write"],
        flow: [[["MAR", "RAM"], R1_SRC, WA_SRC], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { MDR: 42, A0: 0x204 }
      },
      mdrToReg("mvpi2", "D1", 0, ".l")(42)
    ]
  },
  {
    name: "move.b (A0)+, D1", group: "Пересылка",
    about: "То же для байта: читается 1 байт, A0 растёт на 1 (const_sel = 1), в D1 меняется только младший байт.",
    init: { A0: 0x200, D1: 0x300 },
    steps: [
      ...fetch("move.b (A0)+, D1", 0x1218),
      marFrom("mvbpi0", "src", "A0", 0x200),
      {
        mu: "mvbpi1", jump: "+1", rtl: "MDR ← mem.b[MAR] ; A0 ← A0 + 1",
        sig: ["ram_rd", "mem_size=.b", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "sel_r1=src", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=1", "alu_op=ADD", "sel_wa=src", "sel_wb=ALU", "reg_write"],
        flow: [[["MAR", "RAM"], R1_SRC, WA_SRC], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { MDR: 0xab, A0: 0x201 }
      },
      mdrToReg("mvbpi2", "D1", 0x300, ".b", "байт 0xAB: N = 1 по биту 7")(0xab)
    ]
  },
  {
    name: "move.l -(A0), D1", group: "Пересылка",
    about: "Предекремент: сначала A0 ← A0 − 4, и это же значение сразу уходит в MAR. Один выход ALU — два получателя.",
    init: { A0: 0x204, D1: 0 },
    steps: [
      ...fetch("move.l -(A0), D1", 0x2220),
      {
        mu: "mvpd0", jump: "+1", rtl: "A0 ← A0 − 4 ; MAR ← A0 − 4",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=SUB", "sel_wa=src", "sel_wb=ALU", "reg_write", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SRC, WA_SRC], [["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_MAR", "MAR"], ["ALU", "MUX_WB", "RF"]]],
        set: { A0: 0x200, MAR: 0x200 }
      },
      memRead("mvpd1", 42, ".l"),
      mdrToReg("mvpd2", "D1", 0, ".l")(42)
    ]
  },
  {
    name: "move.l 8(A0), D1", group: "Пересылка",
    about: "Смещение 8 лежит в команде: его читают в MDR, расширяют со знаком в SignExt и складывают с A0.",
    init: { A0: 0x200, D1: 0 },
    steps: [
      ...fetch("move.l 8(A0), D1", 0x2228),
      ...ext("dsp", 8, 2, 0x102),
      {
        mu: "dsp0", jump: "+1", rtl: "MAR ← A0 + SignExt(MDR)",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "sel_alu_b=SEXT", "alu_op=ADD", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SRC, ["MDR", "SEXT", "MUX_B", "ALU"]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MAR", "MAR"]]],
        set: { MAR: 0x208 }
      },
      memRead("dsp1", 77, ".l"),
      mdrToReg("dsp2", "D1", 0, ".l")(77)
    ]
  },
  {
    name: "move.l 8(A0,D2), D1", group: "Пересылка",
    about: "Индексный режим: адрес = A0 + D2 + 8. ALU нужен дважды, промежуточная сумма ждёт в TMP.",
    init: { A0: 0x200, D2: 4 },
    steps: [
      ...fetch("move.l 8(A0,D2), D1", 0x2230),
      ...ext("idx", 8, 2, 0x102),
      {
        mu: "idx0", jump: "+1", rtl: "TMP ← A0 + D2",
        sig: ["sel_r1=src", "sel_r2=idx", "sel_alu_a=rdata1", "sel_alu_b=rdata2", "alu_op=ADD", "latch_tmp"],
        flow: [[R1_SRC, R2_IDX], [["RF", "MUX_A", "ALU"], ["RF", "MUX_B", "ALU"]], [["ALU", "TMP"]]],
        set: { TMP: 0x204 }
      },
      {
        mu: "idx1", jump: "+1", rtl: "MAR ← TMP + SignExt(MDR)",
        sig: ["sel_alu_a=TMP", "sel_alu_b=SEXT", "alu_op=ADD", "sel_mar=ALU", "latch_mar"],
        flow: [[["TMP", "MUX_A", "ALU"], ["MDR", "SEXT", "MUX_B", "ALU"]], [["ALU", "MUX_MAR", "MAR"]]],
        set: { MAR: 0x20c }
      },
      memRead("idx2", 99, ".l"),
      mdrToReg("idx3", "D1", 0, ".l")(99)
    ]
  },
  {
    name: "move.l D0, (A1)+", group: "Пересылка",
    about: "Запись в память с постинкрементом: пока RAM пишет, ALU свободен и увеличивает A1.",
    init: { D0: 5, A1: 0x300 },
    steps: [
      ...fetch("move.l D0, (A1)+", 0x22c0),
      marFrom("mvst0", "dst", "A1", 0x300),
      {
        mu: "mvst1", jump: "+1", rtl: "MDR ← D0 ; SR ← NZ, V = C = 0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mdr=ALU", "latch_mdr", "latch_sr"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MDR", "MDR"], ["ALU", "SR"]]],
        set: { MDR: 5, SR: alu("PASS", 5, 0, ".l").sr }
      },
      {
        mu: "mvst2", ...done, rtl: "mem[MAR] ← MDR ; A1 ← A1 + 4",
        sig: ["ram_wr", "mem_size=.l", "sel_r1=dst", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=ADD", "sel_wa=dst", "sel_wb=ALU", "reg_write"],
        flow: [[["MAR", "RAM"], ["MAR", "CMP"], R1_DST, WA_DST], [["MDR", "RAM"], ["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { A1: 0x304 }, label: "5",
        note: "в память: mem[0x300] = 5"
      }
    ]
  },
  {
    name: "movea.l D0, A1", group: "Пересылка",
    about: "Загрузка адресного регистра. Единственная команда, где An — прямой операнд. Флаги не меняются.",
    init: { D0: 0x300 },
    steps: [
      ...fetch("movea.l D0, A1", 0x2240),
      {
        mu: "mva0", ...done, rtl: "A1 ← D0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.l"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST]],
        set: { A1: 0x300 },
        note: "latch_sr = 0 — флаги остались прежними"
      }
    ]
  },
  {
    name: "movea.l 1000, A0", group: "Пересылка",
    about: "Адрес из команды кладётся в A0 прямо из MDR через MUX WB, ALU не нужен.",
    init: { A0: 0 },
    steps: [
      ...fetch("movea.l 1000, A0", 0x207c),
      ...ext("mvai", 1000, 4, 0x102),
      {
        mu: "mvai0", ...done, rtl: "A0 ← MDR",
        sig: ["sel_wb=MDR", "sel_wa=dst", "reg_write", "wr_size=.l"],
        flow: [[["MDR", "MUX_WB", "RF"], WA_DST]],
        set: { A0: 1000 }
      }
    ]
  },

  regReg({
    name: "add.l D0, D1", group: "Арифметика", mu: "add0", opcode: 0xd280, op: "ADD", d0: 5, d1: 7,
    about: "D1 ← D1 + D0. Оба операнда из регистров, всё за один такт.",
    rtl: "D1 ← D1 + D0 ; SR ← NZVC"
  }),
  {
    name: "add.l 10, D0", group: "Арифметика",
    about: "Второй операнд — число из команды: читаем его в MDR и подаём на вход B через imm/ext.",
    init: { D0: 5 },
    steps: [
      ...fetch("add.l 10, D0", 0xd0bc),
      ...ext("addi", 10, 4, 0x102),
      {
        mu: "addi0", ...done, rtl: "D0 ← D0 + MDR ; SR ← NZVC",
        sig: ["sel_r1=dst", "sel_alu_a=rdata1", "sel_alu_b=MDR", "alu_op=ADD", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.l", "latch_sr"],
        flow: [[R1_DST, ["MDR", "MUX_B", "ALU"]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]],
        set: { D0: 15, SR: alu("ADD", 5, 10, ".l").sr }
      }
    ]
  },
  regReg({
    name: "add.b D0, D1", group: "Арифметика", mu: "addb0", opcode: 0xd200, op: "ADD", size: ".b", d0: 1, d1: 0x1ff,
    about: "Сложение младших байтов: 0xFF + 1 = 0x100 не помещается в байт.",
    rtl: "D1[7:0] ← D1[7:0] + D0[7:0] ; SR ← NZVC",
    note: "перенос из бита 7 ушёл в C, а не в старший байт: D1 = 0x100, Z = 1"
  }),
  {
    name: "add.b 1, D1", group: "Арифметика",
    about: "Байтовое число в команде занимает 1 байт: pc_inc = 1. 127 + 1 в байте со знаком — переполнение.",
    init: { D1: 0x7f },
    steps: [
      ...fetch("add.b 1, D1", 0xd23c),
      ...ext("addbi", 1, 1, 0x102),
      {
        mu: "addbi0", ...done, rtl: "D1[7:0] ← D1[7:0] + MDR[7:0] ; SR ← NZVC",
        sig: ["sel_r1=dst", "sel_alu_a=rdata1", "sel_alu_b=MDR", "alu_op=ADD.B", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.b", "latch_sr"],
        flow: [[R1_DST, ["MDR", "MUX_B", "ALU"]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"], WA_DST, ["ALU", "SR"]]],
        set: { D1: merge(0x7f, alu("ADD", 0x7f, 1, ".b").r, ".b"), SR: alu("ADD", 0x7f, 1, ".b").sr },
        note: "127 + 1 = −128 в байте: N = 1, V = 1"
      }
    ]
  },
  regReg({
    name: "sub.l D0, D1", group: "Арифметика", mu: "sub0", opcode: 0x9280, op: "SUB", d0: 5, d1: 7,
    about: "D1 ← D1 − D0. Важен порядок: приёмник на вход A, источник на вход B.",
    rtl: "D1 ← D1 − D0 ; SR ← NZVC"
  }),
  {
    name: "sub.l D0, (A1)", group: "Арифметика",
    about: "Приёмник в памяти: читаем, вычитаем и пишем обратно. Уменьшаемое идёт из MDR на вход A.",
    init: { D0: 5, A1: 0x300 },
    steps: [
      ...fetch("sub.l D0, (A1)", 0x9191),
      marFrom("subm0", "dst", "A1", 0x300),
      memRead("subm1", 20, ".l"),
      {
        mu: "subm2", jump: "+1", rtl: "MDR ← MDR − D0 ; SR ← NZVC",
        sig: ["sel_r2=src", "sel_alu_a=MDR", "sel_alu_b=rdata2", "alu_op=SUB", "sel_mdr=ALU", "latch_mdr", "latch_sr"],
        flow: [[R2_SRC], [["MDR", "MUX_A", "ALU"], ["RF", "MUX_B", "ALU"]], [["ALU", "MUX_MDR", "MDR"], ["ALU", "SR"]]],
        set: { MDR: 15, SR: alu("SUB", 20, 5, ".l").sr }
      },
      {
        mu: "subm3", ...done, rtl: "mem[MAR] ← MDR",
        sig: ["ram_wr", "mem_size=.l"],
        flow: [[["MDR", "RAM"]]],
        set: {}, label: "15", note: "в память: mem[0x300] = 15"
      }
    ]
  },
  unary({
    name: "neg.l D1", group: "Арифметика", mu: "neg0", opcode: 0x4481, op: "NEG", reg: "D1", value: 5,
    about: "Смена знака: 0 − D1. Флаги как у вычитания, C = 1 для любого ненулевого операнда.",
    rtl: "D1 ← 0 − D1 ; SR ← NZVC"
  }),
  regReg({
    name: "mul.l D0, D1", group: "Арифметика", mu: "mul0", opcode: 0x4c00, op: "MUL", d0: 6, d1: 7,
    about: "Умножение: в D1 остаются младшие 32 бита произведения.",
    rtl: "D1 ← D1 × D0 ; SR ← NZ, V = C = 0"
  }),
  regReg({
    name: "div.l D0, D1", group: "Арифметика", mu: "div0", opcode: 0x4c40, op: "DIV", d0: 5, d1: 42,
    about: "Деление: в D1 остаётся частное, остаток отбрасывается.",
    rtl: "D1 ← D1 / D0 ; SR ← NZ, V = C = 0",
    note: "42 / 5 = 8, остаток 2 отброшен"
  }),
  {
    name: "cmp.l D0, D1", group: "Арифметика",
    about: "Вычитание без записи результата: меняются только флаги. Равные числа дают Z = 1.",
    init: { D0: 7, D1: 7 },
    steps: [
      ...fetch("cmp.l D0, D1", 0xb280),
      {
        mu: "cmp0", ...done, rtl: "SR ← флаги(D1 − D0)",
        sig: ["sel_r1=dst", "sel_r2=src", "sel_alu_a=rdata1", "sel_alu_b=rdata2", "alu_op=SUB", "latch_sr"],
        flow: [[R1_DST, R2_SRC], [["RF", "MUX_A", "ALU"], ["RF", "MUX_B", "ALU"]], [["ALU", "SR"]]],
        set: { SR: alu("SUB", 7, 7, ".l").sr }, note: "регистр не пишется: reg_write = 0"
      }
    ]
  },

  regReg({
    name: "and.l D0, D1", group: "Логика", mu: "and0", opcode: 0xc280, op: "AND", d0: 0xf0f0, d1: 0x1234,
    about: "Побитовое И: остаются только биты, которые есть в обоих операндах.",
    rtl: "D1 ← D1 & D0 ; SR ← NZ, V = C = 0"
  }),
  regReg({
    name: "or.l D0, D1", group: "Логика", mu: "or0", opcode: 0x8280, op: "OR", d0: 0x0f00, d1: 0x1234,
    about: "Побитовое ИЛИ: биты из D0 добавляются к D1.",
    rtl: "D1 ← D1 | D0 ; SR ← NZ, V = C = 0"
  }),
  regReg({
    name: "xor.l D0, D1", group: "Логика", mu: "xor0", opcode: 0xb181, op: "XOR", d0: 0xffff, d1: 0x1234,
    about: "Исключающее ИЛИ: биты D1 инвертируются там, где в D0 единицы.",
    rtl: "D1 ← D1 ^ D0 ; SR ← NZ, V = C = 0"
  }),
  unary({
    name: "not.l D1", group: "Логика", mu: "not0", opcode: 0x4681, op: "NOT", reg: "D1", value: 0xf,
    about: "Побитовое НЕ: каждый бит регистра меняется на противоположный.",
    rtl: "D1 ← ~D1 ; SR ← NZ, V = C = 0"
  }),
  unary({
    name: "clr.l D0", group: "Логика", mu: "clr0", opcode: 0x4280, op: "ZERO", reg: "D0", value: 77,
    about: "Обнуление. Старое значение не нужно, поэтому регистр даже не читается: ALU выдаёт ноль.",
    rtl: "D0 ← 0 ; SR ← N = 0, Z = 1, V = C = 0"
  }),
  unary({
    name: "clr.b D0", group: "Логика", mu: "clrb0", opcode: 0x4200, op: "ZERO", size: ".b", reg: "D0", value: 0x1ff,
    about: "Байтовое обнуление: wr_size = .b, поэтому старшие байты D0 сохраняются.",
    rtl: "D0[7:0] ← 0 ; SR ← Z = 1",
    note: "D0 было 0x1FF, стало 0x100"
  }),

  regReg({
    name: "asl.l D0, D1", group: "Сдвиги", mu: "asl0", opcode: 0xe1a1, op: "ASL", d0: 2, d1: 0x40000003,
    about: "Арифметический сдвиг влево на D0 бит. Последний выдвинутый бит попадает в C.",
    rtl: "D1 ← D1 << D0 ; SR ← NZ, C = последний бит, V = 0",
    note: "вышли биты 31 и 30, последний = 1 → C = 1"
  }),
  regReg({
    name: "asr.l D0, D1", group: "Сдвиги", mu: "asr0", opcode: 0xe0a1, op: "ASR", d0: 1, d1: u32(-7),
    about: "Арифметический сдвиг вправо: слева размножается знаковый бит, число остаётся отрицательным.",
    rtl: "D1 ← D1 >> D0 (со знаком) ; SR ← NZ, C",
    note: "−7 >> 1 = −4, выдвинутый бит 1 → C = 1"
  }),
  regReg({
    name: "lsl.l D0, D1", group: "Сдвиги", mu: "lsl0", opcode: 0xe1a9, op: "LSL", d0: 4, d1: 0x123,
    about: "Логический сдвиг влево: справа вдвигаются нули. Для сдвига влево совпадает с asl.",
    rtl: "D1 ← D1 << D0 ; SR ← NZ, C, V = 0"
  }),
  regReg({
    name: "lsr.l D0, D1", group: "Сдвиги", mu: "lsr0", opcode: 0xe0a9, op: "LSR", d0: 1, d1: u32(-7),
    about: "Логический сдвиг вправо: слева вдвигаются нули. Сравни с asr на том же числе.",
    rtl: "D1 ← D1 >>> D0 ; SR ← NZ, C, V = 0",
    note: "знак потерян: число стало большим положительным"
  }),

  {
    name: "jmp label", group: "Переходы",
    about: "Безусловный переход. Адрес метки целиком лежит в команде, читается в MDR и идёт в PC.",
    init: {},
    steps: [
      ...brHead("jmp label", 0x4ef9, "jmp"),
      brRead("jmp1", "+1", undefined),
      brTake("jmp2")
    ]
  },
  {
    name: "beq label", group: "Переходы",
    about: "Условный переход: адрес берётся из extension, MUX COND проверяет флаг Z.",
    init: { SR: "0100" },
    steps: [
      ...brHead("beq label", 0x6700, "beq"),
      brRead("beq1", "cond", "if Z = 0 → fetch0, иначе +1", "Z = 1 — переход будет"),
      brTake("beq2")
    ]
  },
  branch1("bne label", 0x6600, "Z", 0, "0000", "Переход, если Z = 0. Здесь Z = 0, поэтому переход есть."),
  branch1("bmi label", 0x6b00, "N", 1, "1000", "Переход, если результат отрицательный (N = 1)."),
  branch1("bpl label", 0x6a00, "N", 0, "1000", "Переход, если N = 0. Здесь N = 1 — перехода нет: команда короче на такт."),
  branch1("bvs label", 0x6900, "V", 1, "0010", "Переход, если было знаковое переполнение (V = 1)."),
  branch1("bvc label", 0x6800, "V", 0, "0010", "Переход, если V = 0. Здесь V = 1 — перехода нет."),
  branch1("bcs label", 0x6500, "C", 1, "0001", "Переход, если C = 1: при беззнаковом сравнении dst < src."),
  branch1("bcc label", 0x6400, "C", 0, "0001", "Переход, если C = 0. Здесь C = 1 — перехода нет."),
  branchN("blt label", 0x6d00, "1000", "Меньше со знаком: N ≠ V. MUX COND видит один флаг за такт, поэтому проверка идёт цепочкой.", [
    { jt: "if N = 1 → blt_n1, иначе +1", note: "N = 1" },
    { mu: "blt_n1", flag: "V", jt: "if V = 1 → fetch0, иначе +1 → blt_t", note: "V = 0 → N ≠ V, переход" }
  ]),
  branchN("bge label", 0x6c00, "1010", "Больше или равно со знаком: N = V. Здесь N = 1 и V = 1.", [
    { jt: "if N = 1 → bge_n1, иначе +1", note: "N = 1" },
    { mu: "bge_n1", flag: "V", jt: "if V = 0 → fetch0, иначе +1 → bge_t", note: "V = 1 → N = V, переход" }
  ]),
  branchN("bgt label", 0x6e00, "0000", "Больше со знаком: Z = 0 и N = V. Три проверки подряд.", [
    { jt: "if Z = 1 → fetch0, иначе +1", note: "Z = 0" },
    { mu: "bgt_z0", flag: "N", jt: "if N = 1 → bgt_n1, иначе +1", note: "N = 0" },
    { mu: "bgt_n0", flag: "V", jt: "if V = 1 → fetch0, иначе +1 → bgt_t", note: "V = 0 → N = V, переход" }
  ]),
  branchN("ble label", 0x6f00, "1000", "Меньше или равно со знаком: Z = 1 или N ≠ V. Здесь Z = 0, N = 1, V = 0.", [
    { jt: "if Z = 1 → ble_t, иначе +1", note: "Z = 0" },
    { mu: "ble_z0", flag: "N", jt: "if N = 1 → ble_n1, иначе +1", note: "N = 1" },
    { mu: "ble_n1", flag: "V", jt: "if V = 1 → fetch0, иначе +1 → ble_t", note: "V = 0 → N ≠ V, переход" }
  ]),

  {
    name: "move.l D0, -(A7)", group: "Стек и подпрограммы",
    about: "Push в стек: сначала уменьшаем SP на 4, потом пишем D0 по новому адресу.",
    init: { D0: 5, A7: 0x3f0 },
    steps: [
      ...fetch("move.l D0, -(A7)", 0x2f00),
      {
        mu: "push0", jump: "+1", rtl: "A7 ← A7 − 4 ; MAR ← A7 − 4",
        sig: ["sel_r1=A7", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=SUB", "sel_wa=A7", "sel_wb=ALU", "reg_write", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SP, WA_SP], [["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_MAR", "MAR"], ["ALU", "MUX_WB", "RF"]]],
        set: { A7: 0x3ec, MAR: 0x3ec }
      },
      {
        mu: "push1", jump: "+1", rtl: "MDR ← D0 ; SR ← NZ, V = C = 0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mdr=ALU", "latch_mdr", "latch_sr"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MDR", "MDR"], ["ALU", "SR"]]],
        set: { MDR: 5, SR: alu("PASS", 5, 0, ".l").sr }
      },
      {
        mu: "push2", ...done, rtl: "mem[MAR] ← MDR",
        sig: ["ram_wr", "mem_size=.l"],
        flow: [[["MAR", "RAM"], ["MAR", "CMP"]], [["MDR", "RAM"]]],
        set: {}, label: "5", note: "в память: mem[0x3EC] = 5"
      }
    ]
  },
  {
    name: "jsr label", group: "Стек и подпрограммы",
    about: "Вызов подпрограммы: адрес возврата уходит в стек через A7, адрес перехода ждёт в TMP.",
    init: { A7: 0x3f0 },
    steps: [
      ...fetch("jsr label", 0x4eb9),
      ...ext("jsr", 0x400, 4, 0x102),
      {
        mu: "jsr0", jump: "+1", rtl: "TMP ← MDR",
        sig: ["sel_alu_b=MDR", "alu_op=PASS_B", "latch_tmp"],
        flow: [[["MDR", "MUX_B", "ALU"]], [["ALU", "TMP"]]],
        set: { TMP: 0x400 }
      },
      {
        mu: "jsr1", jump: "+1", rtl: "A7 ← A7 − 4 ; MAR ← A7 − 4",
        sig: ["sel_r1=A7", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=SUB", "sel_wa=A7", "sel_wb=ALU", "reg_write", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SP, WA_SP], [["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_MAR", "MAR"], ["ALU", "MUX_WB", "RF"]]],
        set: { A7: 0x3ec, MAR: 0x3ec }
      },
      {
        mu: "jsr2", jump: "+1", rtl: "MDR ← PC",
        sig: ["sel_alu_a=PC", "alu_op=PASS_A", "sel_mdr=ALU", "latch_mdr"],
        flow: [[["PC", "MUX_A", "ALU"]], [["ALU", "MUX_MDR", "MDR"]]],
        set: { MDR: 0x106 }
      },
      {
        mu: "jsr3", jump: "+1", rtl: "mem[MAR] ← MDR",
        sig: ["ram_wr", "mem_size=.l"],
        flow: [[["MDR", "RAM"]]],
        set: {}, label: "0x106", note: "адрес возврата в стеке: mem[0x3EC] = 0x106"
      },
      {
        mu: "jsr4", ...done, rtl: "PC ← TMP",
        sig: ["sel_alu_a=TMP", "alu_op=PASS_A", "sel_pc=ALU", "latch_pc"],
        flow: [[["TMP", "MUX_A", "ALU"]], [["ALU", "MUX_PC", "PC"]]],
        set: { PC: 0x400 }
      }
    ]
  },
  {
    name: "rts", group: "Стек и подпрограммы",
    about: "Возврат: достаём адрес из стека и увеличиваем SP.",
    init: { A7: 0x3ec, PC: 0x400 },
    steps: [
      ...fetch("rts", 0x4e75, 0x400),
      marFrom("rts0", "A7", "A7", 0x3ec),
      {
        mu: "rts1", jump: "+1", rtl: "MDR ← mem[MAR] ; A7 ← A7 + 4",
        sig: ["ram_rd", "mem_size=.l", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "sel_r1=A7", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=ADD", "sel_wa=A7", "sel_wb=ALU", "reg_write"],
        flow: [[["MAR", "RAM"], R1_SP, WA_SP], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { MDR: 0x106, A7: 0x3f0 }
      },
      {
        mu: "rts2", ...done, rtl: "PC ← MDR",
        sig: ["sel_pc=MDR", "latch_pc"],
        flow: [[["MDR", "MUX_PC", "PC"]]],
        set: { PC: 0x106 }
      }
    ]
  },
  {
    name: "link A6, -8", group: "Стек и подпрограммы",
    about: "Создание стекового кадра: старый A6 — в стек, A6 ← SP, затем SP сдвигается на −8 под локальные переменные.",
    init: { A6: 0x3fc, A7: 0x3f0 },
    steps: [
      ...fetch("link A6, -8", 0x4e56),
      {
        mu: "link0", jump: "+1", rtl: "A7 ← A7 − 4 ; MAR ← A7 − 4",
        sig: ["sel_r1=A7", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=SUB", "sel_wa=A7", "sel_wb=ALU", "reg_write", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SP, WA_SP], [["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_MAR", "MAR"], ["ALU", "MUX_WB", "RF"]]],
        set: { A7: 0x3ec, MAR: 0x3ec }
      },
      {
        mu: "link1", jump: "+1", rtl: "MDR ← A6",
        sig: ["sel_r1=dst", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mdr=ALU", "latch_mdr"],
        flow: [[R1_DST], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MDR", "MDR"]]],
        set: { MDR: 0x3fc }
      },
      {
        mu: "link2", jump: "+1", rtl: "mem[MAR] ← MDR ; A6 ← A7",
        sig: ["ram_wr", "mem_size=.l", "sel_r1=A7", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_wa=dst", "sel_wb=ALU", "reg_write", "wr_size=.l"],
        flow: [[["MDR", "RAM"], R1_SP, WA_DST], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { A6: 0x3ec },
        note: "старый A6 в стеке: mem[0x3EC] = 0x3FC"
      },
      ...ext("link", 0xfff8, 2, 0x102),
      {
        mu: "link3", ...done, rtl: "A7 ← A7 + SignExt(MDR)",
        sig: ["sel_r1=A7", "sel_alu_a=rdata1", "sel_alu_b=SEXT", "alu_op=ADD", "sel_wa=A7", "sel_wb=ALU", "reg_write", "wr_size=.l"],
        flow: [[R1_SP, WA_SP, ["MDR", "SEXT", "MUX_B", "ALU"]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { A7: 0x3e4 },
        note: "SignExt(0xFFF8) = −8: под локальные переменные 8 байт"
      }
    ]
  },
  {
    name: "unlk A6", group: "Стек и подпрограммы",
    about: "Удаление кадра: SP ← A6 + 4, а A6 восстанавливается из стека. Три шага сжаты в три такта.",
    init: { A6: 0x3ec, A7: 0x3e4 },
    steps: [
      ...fetch("unlk A6", 0x4e5e),
      marFrom("unlk0", "dst", "A6", 0x3ec),
      {
        mu: "unlk1", jump: "+1", rtl: "MDR ← mem[MAR] ; A7 ← A6 + 4",
        sig: ["ram_rd", "mem_size=.l", "sel_mem_in=RAM", "sel_mdr=MEM", "latch_mdr", "sel_r1=dst", "sel_alu_a=rdata1", "sel_alu_b=CONST", "const_sel=4", "alu_op=ADD", "sel_wa=A7", "sel_wb=ALU", "reg_write", "wr_size=.l"],
        flow: [[["MAR", "RAM"], R1_DST, WA_SP], [["RAM", "MUX_MEM", "MUX_MDR", "MDR"], ["RF", "MUX_A", "ALU"], ["CONST", "MUX_B", "ALU"]], [["ALU", "MUX_WB", "RF"]]],
        set: { MDR: 0x3fc, A7: 0x3f0 }
      },
      {
        mu: "unlk2", ...done, rtl: "A6 ← MDR",
        sig: ["sel_wb=MDR", "sel_wa=dst", "reg_write", "wr_size=.l"],
        flow: [[["MDR", "MUX_WB", "RF"], WA_DST]],
        set: { A6: 0x3fc }
      }
    ]
  },

  {
    name: "move.l D0, (A1) → 0x84", group: "Ввод-вывод",
    about: "Вывод через MMIO: A1 = 0x84, Address Decoder поднимает is_out, и вместо ram_wr идёт out_wr.",
    init: { D0: 5, A1: 0x84 },
    steps: [
      ...fetch("move.l D0, (A1)", 0x2280),
      marFrom("out0", "dst", "A1", 0x84),
      {
        mu: "out1", jump: "cond", jumpText: "if is_out → out3", rtl: "MDR ← D0 ; SR ← NZ, V = C = 0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mdr=ALU", "latch_mdr", "latch_sr"],
        flow: [[R1_SRC, ["MAR", "CMP", "st_cmp"]], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MDR", "MDR"], ["ALU", "SR"]]],
        set: { MDR: 5, SR: alu("PASS", 5, 0, ".l").sr }, note: "адрес 0x84 → is_out = 1"
      },
      {
        mu: "out3", ...done, rtl: "OUT ← MDR",
        sig: ["out_wr"],
        flow: [[["MDR", "OUT"]]],
        set: { OUT: 5 }
      }
    ]
  },
  {
    name: "move.l (A0), D0 ← 0x80", group: "Ввод-вывод",
    about: "Ввод через MMIO: A0 = 0x80, Address Decoder поднимает is_in, данные идут из порта ввода.",
    init: { A0: 0x80, IN: 17 },
    steps: [
      ...fetch("move.l (A0), D0", 0x2010),
      {
        mu: "in0", jump: "cond", jumpText: "if is_in → in1", rtl: "MAR ← A0",
        sig: ["sel_r1=src", "sel_alu_a=rdata1", "alu_op=PASS_A", "sel_mar=ALU", "latch_mar"],
        flow: [[R1_SRC], [["RF", "MUX_A", "ALU"]], [["ALU", "MUX_MAR", "MAR"]], [["MAR", "CMP", "st_cmp"]]],
        set: { MAR: 0x80 }, note: "адрес 0x80 → is_in = 1"
      },
      {
        mu: "in1", jump: "+1", rtl: "MDR ← IN",
        sig: ["in_rd", "sel_mem_in=IN", "sel_mdr=MEM", "latch_mdr"],
        flow: [[["IN", "MUX_MEM", "MUX_MDR", "MDR"]]],
        set: { MDR: 17 }
      },
      mdrToReg("in2", "D0", 0, ".l")(17)
    ]
  },

  {
    name: "halt", group: "Прочее",
    about: "Остановка. Микрокоманда переходит сама на себя: тракт данных больше ничего не делает.",
    init: {},
    steps: [
      ...fetch("halt", 0x4e72),
      {
        mu: "halt0", jump: "next", jumpText: "next → halt0 (цикл на месте)", rtl: "остановка процессора",
        sig: [],
        flow: [[]],
        set: {}, label: "", after: "halt0",
        note: "симулятор фиксирует остановку"
      }
    ]
  }
];
