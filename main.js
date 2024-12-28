"use strict";
(() => {
  // lib/zipjs/lib/core/streams/codecs/deflate.js
  var MAX_BITS = 15;
  var D_CODES = 30;
  var BL_CODES = 19;
  var LENGTH_CODES = 29;
  var LITERALS = 256;
  var L_CODES = LITERALS + 1 + LENGTH_CODES;
  var HEAP_SIZE = 2 * L_CODES + 1;
  var END_BLOCK = 256;
  var MAX_BL_BITS = 7;
  var REP_3_6 = 16;
  var REPZ_3_10 = 17;
  var REPZ_11_138 = 18;
  var Buf_size = 8 * 2;
  var Z_DEFAULT_COMPRESSION = -1;
  var Z_FILTERED = 1;
  var Z_HUFFMAN_ONLY = 2;
  var Z_DEFAULT_STRATEGY = 0;
  var Z_NO_FLUSH = 0;
  var Z_PARTIAL_FLUSH = 1;
  var Z_FULL_FLUSH = 3;
  var Z_FINISH = 4;
  var Z_OK = 0;
  var Z_STREAM_END = 1;
  var Z_NEED_DICT = 2;
  var Z_STREAM_ERROR = -2;
  var Z_DATA_ERROR = -3;
  var Z_BUF_ERROR = -5;
  function extractArray(array) {
    return flatArray(array.map(([length, value]) => new Array(length).fill(value, 0, length)));
  }
  function flatArray(array) {
    return array.reduce((a, b) => a.concat(Array.isArray(b) ? flatArray(b) : b), []);
  }
  var _dist_code = [0, 1, 2, 3].concat(...extractArray([
    [2, 4],
    [2, 5],
    [4, 6],
    [4, 7],
    [8, 8],
    [8, 9],
    [16, 10],
    [16, 11],
    [32, 12],
    [32, 13],
    [64, 14],
    [64, 15],
    [2, 0],
    [1, 16],
    [1, 17],
    [2, 18],
    [2, 19],
    [4, 20],
    [4, 21],
    [8, 22],
    [8, 23],
    [16, 24],
    [16, 25],
    [32, 26],
    [32, 27],
    [64, 28],
    [64, 29]
  ]));
  function Tree() {
    const that = this;
    function gen_bitlen2(s) {
      const tree = that.dyn_tree;
      const stree = that.stat_desc.static_tree;
      const extra = that.stat_desc.extra_bits;
      const base = that.stat_desc.extra_base;
      const max_length = that.stat_desc.max_length;
      let h;
      let n, m;
      let bits;
      let xbits;
      let f;
      let overflow = 0;
      for (bits = 0; bits <= MAX_BITS; bits++)
        s.bl_count[bits] = 0;
      tree[s.heap[s.heap_max] * 2 + 1] = 0;
      for (h = s.heap_max + 1; h < HEAP_SIZE; h++) {
        n = s.heap[h];
        bits = tree[tree[n * 2 + 1] * 2 + 1] + 1;
        if (bits > max_length) {
          bits = max_length;
          overflow++;
        }
        tree[n * 2 + 1] = bits;
        if (n > that.max_code)
          continue;
        s.bl_count[bits]++;
        xbits = 0;
        if (n >= base)
          xbits = extra[n - base];
        f = tree[n * 2];
        s.opt_len += f * (bits + xbits);
        if (stree)
          s.static_len += f * (stree[n * 2 + 1] + xbits);
      }
      if (overflow === 0)
        return;
      do {
        bits = max_length - 1;
        while (s.bl_count[bits] === 0)
          bits--;
        s.bl_count[bits]--;
        s.bl_count[bits + 1] += 2;
        s.bl_count[max_length]--;
        overflow -= 2;
      } while (overflow > 0);
      for (bits = max_length; bits !== 0; bits--) {
        n = s.bl_count[bits];
        while (n !== 0) {
          m = s.heap[--h];
          if (m > that.max_code)
            continue;
          if (tree[m * 2 + 1] != bits) {
            s.opt_len += (bits - tree[m * 2 + 1]) * tree[m * 2];
            tree[m * 2 + 1] = bits;
          }
          n--;
        }
      }
    }
    function bi_reverse2(code2, len) {
      let res = 0;
      do {
        res |= code2 & 1;
        code2 >>>= 1;
        res <<= 1;
      } while (--len > 0);
      return res >>> 1;
    }
    function gen_codes2(tree, max_code, bl_count) {
      const next_code = [];
      let code2 = 0;
      let bits;
      let n;
      let len;
      for (bits = 1; bits <= MAX_BITS; bits++) {
        next_code[bits] = code2 = code2 + bl_count[bits - 1] << 1;
      }
      for (n = 0; n <= max_code; n++) {
        len = tree[n * 2 + 1];
        if (len === 0)
          continue;
        tree[n * 2] = bi_reverse2(next_code[len]++, len);
      }
    }
    that.build_tree = function(s) {
      const tree = that.dyn_tree;
      const stree = that.stat_desc.static_tree;
      const elems = that.stat_desc.elems;
      let n, m;
      let max_code = -1;
      let node;
      s.heap_len = 0;
      s.heap_max = HEAP_SIZE;
      for (n = 0; n < elems; n++) {
        if (tree[n * 2] !== 0) {
          s.heap[++s.heap_len] = max_code = n;
          s.depth[n] = 0;
        } else {
          tree[n * 2 + 1] = 0;
        }
      }
      while (s.heap_len < 2) {
        node = s.heap[++s.heap_len] = max_code < 2 ? ++max_code : 0;
        tree[node * 2] = 1;
        s.depth[node] = 0;
        s.opt_len--;
        if (stree)
          s.static_len -= stree[node * 2 + 1];
      }
      that.max_code = max_code;
      for (n = Math.floor(s.heap_len / 2); n >= 1; n--)
        s.pqdownheap(tree, n);
      node = elems;
      do {
        n = s.heap[1];
        s.heap[1] = s.heap[s.heap_len--];
        s.pqdownheap(tree, 1);
        m = s.heap[1];
        s.heap[--s.heap_max] = n;
        s.heap[--s.heap_max] = m;
        tree[node * 2] = tree[n * 2] + tree[m * 2];
        s.depth[node] = Math.max(s.depth[n], s.depth[m]) + 1;
        tree[n * 2 + 1] = tree[m * 2 + 1] = node;
        s.heap[1] = node++;
        s.pqdownheap(tree, 1);
      } while (s.heap_len >= 2);
      s.heap[--s.heap_max] = s.heap[1];
      gen_bitlen2(s);
      gen_codes2(tree, that.max_code, s.bl_count);
    };
  }
  Tree._length_code = [0, 1, 2, 3, 4, 5, 6, 7].concat(...extractArray([
    [2, 8],
    [2, 9],
    [2, 10],
    [2, 11],
    [4, 12],
    [4, 13],
    [4, 14],
    [4, 15],
    [8, 16],
    [8, 17],
    [8, 18],
    [8, 19],
    [16, 20],
    [16, 21],
    [16, 22],
    [16, 23],
    [32, 24],
    [32, 25],
    [32, 26],
    [31, 27],
    [1, 28]
  ]));
  Tree.base_length = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 0];
  Tree.base_dist = [
    0,
    1,
    2,
    3,
    4,
    6,
    8,
    12,
    16,
    24,
    32,
    48,
    64,
    96,
    128,
    192,
    256,
    384,
    512,
    768,
    1024,
    1536,
    2048,
    3072,
    4096,
    6144,
    8192,
    12288,
    16384,
    24576
  ];
  Tree.d_code = function(dist) {
    return dist < 256 ? _dist_code[dist] : _dist_code[256 + (dist >>> 7)];
  };
  Tree.extra_lbits = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
  Tree.extra_dbits = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
  Tree.extra_blbits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7];
  Tree.bl_order = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  function StaticTree(static_tree, extra_bits, extra_base, elems, max_length) {
    const that = this;
    that.static_tree = static_tree;
    that.extra_bits = extra_bits;
    that.extra_base = extra_base;
    that.elems = elems;
    that.max_length = max_length;
  }
  var static_ltree2_first_part = [
    12,
    140,
    76,
    204,
    44,
    172,
    108,
    236,
    28,
    156,
    92,
    220,
    60,
    188,
    124,
    252,
    2,
    130,
    66,
    194,
    34,
    162,
    98,
    226,
    18,
    146,
    82,
    210,
    50,
    178,
    114,
    242,
    10,
    138,
    74,
    202,
    42,
    170,
    106,
    234,
    26,
    154,
    90,
    218,
    58,
    186,
    122,
    250,
    6,
    134,
    70,
    198,
    38,
    166,
    102,
    230,
    22,
    150,
    86,
    214,
    54,
    182,
    118,
    246,
    14,
    142,
    78,
    206,
    46,
    174,
    110,
    238,
    30,
    158,
    94,
    222,
    62,
    190,
    126,
    254,
    1,
    129,
    65,
    193,
    33,
    161,
    97,
    225,
    17,
    145,
    81,
    209,
    49,
    177,
    113,
    241,
    9,
    137,
    73,
    201,
    41,
    169,
    105,
    233,
    25,
    153,
    89,
    217,
    57,
    185,
    121,
    249,
    5,
    133,
    69,
    197,
    37,
    165,
    101,
    229,
    21,
    149,
    85,
    213,
    53,
    181,
    117,
    245,
    13,
    141,
    77,
    205,
    45,
    173,
    109,
    237,
    29,
    157,
    93,
    221,
    61,
    189,
    125,
    253,
    19,
    275,
    147,
    403,
    83,
    339,
    211,
    467,
    51,
    307,
    179,
    435,
    115,
    371,
    243,
    499,
    11,
    267,
    139,
    395,
    75,
    331,
    203,
    459,
    43,
    299,
    171,
    427,
    107,
    363,
    235,
    491,
    27,
    283,
    155,
    411,
    91,
    347,
    219,
    475,
    59,
    315,
    187,
    443,
    123,
    379,
    251,
    507,
    7,
    263,
    135,
    391,
    71,
    327,
    199,
    455,
    39,
    295,
    167,
    423,
    103,
    359,
    231,
    487,
    23,
    279,
    151,
    407,
    87,
    343,
    215,
    471,
    55,
    311,
    183,
    439,
    119,
    375,
    247,
    503,
    15,
    271,
    143,
    399,
    79,
    335,
    207,
    463,
    47,
    303,
    175,
    431,
    111,
    367,
    239,
    495,
    31,
    287,
    159,
    415,
    95,
    351,
    223,
    479,
    63,
    319,
    191,
    447,
    127,
    383,
    255,
    511,
    0,
    64,
    32,
    96,
    16,
    80,
    48,
    112,
    8,
    72,
    40,
    104,
    24,
    88,
    56,
    120,
    4,
    68,
    36,
    100,
    20,
    84,
    52,
    116,
    3,
    131,
    67,
    195,
    35,
    163,
    99,
    227
  ];
  var static_ltree2_second_part = extractArray([[144, 8], [112, 9], [24, 7], [8, 8]]);
  StaticTree.static_ltree = flatArray(static_ltree2_first_part.map((value, index) => [value, static_ltree2_second_part[index]]));
  var static_dtree_first_part = [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23];
  var static_dtree_second_part = extractArray([[30, 5]]);
  StaticTree.static_dtree = flatArray(static_dtree_first_part.map((value, index) => [value, static_dtree_second_part[index]]));
  StaticTree.static_l_desc = new StaticTree(StaticTree.static_ltree, Tree.extra_lbits, LITERALS + 1, L_CODES, MAX_BITS);
  StaticTree.static_d_desc = new StaticTree(StaticTree.static_dtree, Tree.extra_dbits, 0, D_CODES, MAX_BITS);
  StaticTree.static_bl_desc = new StaticTree(null, Tree.extra_blbits, 0, BL_CODES, MAX_BL_BITS);
  var MAX_MEM_LEVEL = 9;
  var DEF_MEM_LEVEL = 8;
  function Config(good_length, max_lazy, nice_length, max_chain, func) {
    const that = this;
    that.good_length = good_length;
    that.max_lazy = max_lazy;
    that.nice_length = nice_length;
    that.max_chain = max_chain;
    that.func = func;
  }
  var STORED = 0;
  var FAST = 1;
  var SLOW = 2;
  var config_table = [
    new Config(0, 0, 0, 0, STORED),
    new Config(4, 4, 8, 4, FAST),
    new Config(4, 5, 16, 8, FAST),
    new Config(4, 6, 32, 32, FAST),
    new Config(4, 4, 16, 16, SLOW),
    new Config(8, 16, 32, 32, SLOW),
    new Config(8, 16, 128, 128, SLOW),
    new Config(8, 32, 128, 256, SLOW),
    new Config(32, 128, 258, 1024, SLOW),
    new Config(32, 258, 258, 4096, SLOW)
  ];
  var z_errmsg = [
    "need dictionary",
    // Z_NEED_DICT
    // 2
    "stream end",
    // Z_STREAM_END 1
    "",
    // Z_OK 0
    "",
    // Z_ERRNO (-1)
    "stream error",
    // Z_STREAM_ERROR (-2)
    "data error",
    // Z_DATA_ERROR (-3)
    "",
    // Z_MEM_ERROR (-4)
    "buffer error",
    // Z_BUF_ERROR (-5)
    "",
    // Z_VERSION_ERROR (-6)
    ""
  ];
  var NeedMore = 0;
  var BlockDone = 1;
  var FinishStarted = 2;
  var FinishDone = 3;
  var PRESET_DICT = 32;
  var INIT_STATE = 42;
  var BUSY_STATE = 113;
  var FINISH_STATE = 666;
  var Z_DEFLATED = 8;
  var STORED_BLOCK = 0;
  var STATIC_TREES = 1;
  var DYN_TREES = 2;
  var MIN_MATCH = 3;
  var MAX_MATCH = 258;
  var MIN_LOOKAHEAD = MAX_MATCH + MIN_MATCH + 1;
  function smaller(tree, n, m, depth) {
    const tn2 = tree[n * 2];
    const tm2 = tree[m * 2];
    return tn2 < tm2 || tn2 == tm2 && depth[n] <= depth[m];
  }
  function Deflate() {
    const that = this;
    let strm;
    let status;
    let pending_buf_size;
    let last_flush;
    let w_size;
    let w_bits;
    let w_mask;
    let win;
    let window_size;
    let prev;
    let head;
    let ins_h;
    let hash_size;
    let hash_bits;
    let hash_mask;
    let hash_shift;
    let block_start;
    let match_length;
    let prev_match;
    let match_available;
    let strstart;
    let match_start;
    let lookahead;
    let prev_length;
    let max_chain_length;
    let max_lazy_match;
    let level;
    let strategy;
    let good_match;
    let nice_match;
    let dyn_ltree;
    let dyn_dtree;
    let bl_tree;
    const l_desc = new Tree();
    const d_desc = new Tree();
    const bl_desc = new Tree();
    that.depth = [];
    let lit_bufsize;
    let last_lit;
    let matches;
    let last_eob_len;
    let bi_buf;
    let bi_valid;
    that.bl_count = [];
    that.heap = [];
    dyn_ltree = [];
    dyn_dtree = [];
    bl_tree = [];
    function lm_init2() {
      window_size = 2 * w_size;
      head[hash_size - 1] = 0;
      for (let i = 0; i < hash_size - 1; i++) {
        head[i] = 0;
      }
      max_lazy_match = config_table[level].max_lazy;
      good_match = config_table[level].good_length;
      nice_match = config_table[level].nice_length;
      max_chain_length = config_table[level].max_chain;
      strstart = 0;
      block_start = 0;
      lookahead = 0;
      match_length = prev_length = MIN_MATCH - 1;
      match_available = 0;
      ins_h = 0;
    }
    function init_block2() {
      let i;
      for (i = 0; i < L_CODES; i++)
        dyn_ltree[i * 2] = 0;
      for (i = 0; i < D_CODES; i++)
        dyn_dtree[i * 2] = 0;
      for (i = 0; i < BL_CODES; i++)
        bl_tree[i * 2] = 0;
      dyn_ltree[END_BLOCK * 2] = 1;
      that.opt_len = that.static_len = 0;
      last_lit = matches = 0;
    }
    function tr_init() {
      l_desc.dyn_tree = dyn_ltree;
      l_desc.stat_desc = StaticTree.static_l_desc;
      d_desc.dyn_tree = dyn_dtree;
      d_desc.stat_desc = StaticTree.static_d_desc;
      bl_desc.dyn_tree = bl_tree;
      bl_desc.stat_desc = StaticTree.static_bl_desc;
      bi_buf = 0;
      bi_valid = 0;
      last_eob_len = 8;
      init_block2();
    }
    that.pqdownheap = function(tree, k) {
      const heap = that.heap;
      const v = heap[k];
      let j = k << 1;
      while (j <= that.heap_len) {
        if (j < that.heap_len && smaller(tree, heap[j + 1], heap[j], that.depth)) {
          j++;
        }
        if (smaller(tree, v, heap[j], that.depth))
          break;
        heap[k] = heap[j];
        k = j;
        j <<= 1;
      }
      heap[k] = v;
    };
    function scan_tree2(tree, max_code) {
      let prevlen = -1;
      let curlen;
      let nextlen = tree[0 * 2 + 1];
      let count = 0;
      let max_count = 7;
      let min_count = 4;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      }
      tree[(max_code + 1) * 2 + 1] = 65535;
      for (let n = 0; n <= max_code; n++) {
        curlen = nextlen;
        nextlen = tree[(n + 1) * 2 + 1];
        if (++count < max_count && curlen == nextlen) {
          continue;
        } else if (count < min_count) {
          bl_tree[curlen * 2] += count;
        } else if (curlen !== 0) {
          if (curlen != prevlen)
            bl_tree[curlen * 2]++;
          bl_tree[REP_3_6 * 2]++;
        } else if (count <= 10) {
          bl_tree[REPZ_3_10 * 2]++;
        } else {
          bl_tree[REPZ_11_138 * 2]++;
        }
        count = 0;
        prevlen = curlen;
        if (nextlen === 0) {
          max_count = 138;
          min_count = 3;
        } else if (curlen == nextlen) {
          max_count = 6;
          min_count = 3;
        } else {
          max_count = 7;
          min_count = 4;
        }
      }
    }
    function build_bl_tree2() {
      let max_blindex;
      scan_tree2(dyn_ltree, l_desc.max_code);
      scan_tree2(dyn_dtree, d_desc.max_code);
      bl_desc.build_tree(that);
      for (max_blindex = BL_CODES - 1; max_blindex >= 3; max_blindex--) {
        if (bl_tree[Tree.bl_order[max_blindex] * 2 + 1] !== 0)
          break;
      }
      that.opt_len += 3 * (max_blindex + 1) + 5 + 5 + 4;
      return max_blindex;
    }
    function put_byte2(p) {
      that.pending_buf[that.pending++] = p;
    }
    function put_short2(w) {
      put_byte2(w & 255);
      put_byte2(w >>> 8 & 255);
    }
    function putShortMSB2(b) {
      put_byte2(b >> 8 & 255);
      put_byte2(b & 255 & 255);
    }
    function send_bits2(value, length) {
      let val;
      const len = length;
      if (bi_valid > Buf_size - len) {
        val = value;
        bi_buf |= val << bi_valid & 65535;
        put_short2(bi_buf);
        bi_buf = val >>> Buf_size - bi_valid;
        bi_valid += len - Buf_size;
      } else {
        bi_buf |= value << bi_valid & 65535;
        bi_valid += len;
      }
    }
    function send_code2(c, tree) {
      const c2 = c * 2;
      send_bits2(tree[c2] & 65535, tree[c2 + 1] & 65535);
    }
    function send_tree2(tree, max_code) {
      let n;
      let prevlen = -1;
      let curlen;
      let nextlen = tree[0 * 2 + 1];
      let count = 0;
      let max_count = 7;
      let min_count = 4;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      }
      for (n = 0; n <= max_code; n++) {
        curlen = nextlen;
        nextlen = tree[(n + 1) * 2 + 1];
        if (++count < max_count && curlen == nextlen) {
          continue;
        } else if (count < min_count) {
          do {
            send_code2(curlen, bl_tree);
          } while (--count !== 0);
        } else if (curlen !== 0) {
          if (curlen != prevlen) {
            send_code2(curlen, bl_tree);
            count--;
          }
          send_code2(REP_3_6, bl_tree);
          send_bits2(count - 3, 2);
        } else if (count <= 10) {
          send_code2(REPZ_3_10, bl_tree);
          send_bits2(count - 3, 3);
        } else {
          send_code2(REPZ_11_138, bl_tree);
          send_bits2(count - 11, 7);
        }
        count = 0;
        prevlen = curlen;
        if (nextlen === 0) {
          max_count = 138;
          min_count = 3;
        } else if (curlen == nextlen) {
          max_count = 6;
          min_count = 3;
        } else {
          max_count = 7;
          min_count = 4;
        }
      }
    }
    function send_all_trees2(lcodes, dcodes, blcodes) {
      let rank2;
      send_bits2(lcodes - 257, 5);
      send_bits2(dcodes - 1, 5);
      send_bits2(blcodes - 4, 4);
      for (rank2 = 0; rank2 < blcodes; rank2++) {
        send_bits2(bl_tree[Tree.bl_order[rank2] * 2 + 1], 3);
      }
      send_tree2(dyn_ltree, lcodes - 1);
      send_tree2(dyn_dtree, dcodes - 1);
    }
    function bi_flush2() {
      if (bi_valid == 16) {
        put_short2(bi_buf);
        bi_buf = 0;
        bi_valid = 0;
      } else if (bi_valid >= 8) {
        put_byte2(bi_buf & 255);
        bi_buf >>>= 8;
        bi_valid -= 8;
      }
    }
    function _tr_align2() {
      send_bits2(STATIC_TREES << 1, 3);
      send_code2(END_BLOCK, StaticTree.static_ltree);
      bi_flush2();
      if (1 + last_eob_len + 10 - bi_valid < 9) {
        send_bits2(STATIC_TREES << 1, 3);
        send_code2(END_BLOCK, StaticTree.static_ltree);
        bi_flush2();
      }
      last_eob_len = 7;
    }
    function _tr_tally2(dist, lc) {
      let out_length, in_length, dcode;
      that.dist_buf[last_lit] = dist;
      that.lc_buf[last_lit] = lc & 255;
      last_lit++;
      if (dist === 0) {
        dyn_ltree[lc * 2]++;
      } else {
        matches++;
        dist--;
        dyn_ltree[(Tree._length_code[lc] + LITERALS + 1) * 2]++;
        dyn_dtree[Tree.d_code(dist) * 2]++;
      }
      if ((last_lit & 8191) === 0 && level > 2) {
        out_length = last_lit * 8;
        in_length = strstart - block_start;
        for (dcode = 0; dcode < D_CODES; dcode++) {
          out_length += dyn_dtree[dcode * 2] * (5 + Tree.extra_dbits[dcode]);
        }
        out_length >>>= 3;
        if (matches < Math.floor(last_lit / 2) && out_length < Math.floor(in_length / 2))
          return true;
      }
      return last_lit == lit_bufsize - 1;
    }
    function compress_block2(ltree, dtree) {
      let dist;
      let lc;
      let lx = 0;
      let code2;
      let extra;
      if (last_lit !== 0) {
        do {
          dist = that.dist_buf[lx];
          lc = that.lc_buf[lx];
          lx++;
          if (dist === 0) {
            send_code2(lc, ltree);
          } else {
            code2 = Tree._length_code[lc];
            send_code2(code2 + LITERALS + 1, ltree);
            extra = Tree.extra_lbits[code2];
            if (extra !== 0) {
              lc -= Tree.base_length[code2];
              send_bits2(lc, extra);
            }
            dist--;
            code2 = Tree.d_code(dist);
            send_code2(code2, dtree);
            extra = Tree.extra_dbits[code2];
            if (extra !== 0) {
              dist -= Tree.base_dist[code2];
              send_bits2(dist, extra);
            }
          }
        } while (lx < last_lit);
      }
      send_code2(END_BLOCK, ltree);
      last_eob_len = ltree[END_BLOCK * 2 + 1];
    }
    function bi_windup2() {
      if (bi_valid > 8) {
        put_short2(bi_buf);
      } else if (bi_valid > 0) {
        put_byte2(bi_buf & 255);
      }
      bi_buf = 0;
      bi_valid = 0;
    }
    function copy_block(buf, len, header) {
      bi_windup2();
      last_eob_len = 8;
      if (header) {
        put_short2(len);
        put_short2(~len);
      }
      that.pending_buf.set(win.subarray(buf, buf + len), that.pending);
      that.pending += len;
    }
    function _tr_stored_block2(buf, stored_len, eof) {
      send_bits2((STORED_BLOCK << 1) + (eof ? 1 : 0), 3);
      copy_block(buf, stored_len, true);
    }
    function _tr_flush_block2(buf, stored_len, eof) {
      let opt_lenb, static_lenb;
      let max_blindex = 0;
      if (level > 0) {
        l_desc.build_tree(that);
        d_desc.build_tree(that);
        max_blindex = build_bl_tree2();
        opt_lenb = that.opt_len + 3 + 7 >>> 3;
        static_lenb = that.static_len + 3 + 7 >>> 3;
        if (static_lenb <= opt_lenb)
          opt_lenb = static_lenb;
      } else {
        opt_lenb = static_lenb = stored_len + 5;
      }
      if (stored_len + 4 <= opt_lenb && buf != -1) {
        _tr_stored_block2(buf, stored_len, eof);
      } else if (static_lenb == opt_lenb) {
        send_bits2((STATIC_TREES << 1) + (eof ? 1 : 0), 3);
        compress_block2(StaticTree.static_ltree, StaticTree.static_dtree);
      } else {
        send_bits2((DYN_TREES << 1) + (eof ? 1 : 0), 3);
        send_all_trees2(l_desc.max_code + 1, d_desc.max_code + 1, max_blindex + 1);
        compress_block2(dyn_ltree, dyn_dtree);
      }
      init_block2();
      if (eof) {
        bi_windup2();
      }
    }
    function flush_block_only2(eof) {
      _tr_flush_block2(block_start >= 0 ? block_start : -1, strstart - block_start, eof);
      block_start = strstart;
      strm.flush_pending();
    }
    function fill_window2() {
      let n, m;
      let p;
      let more;
      do {
        more = window_size - lookahead - strstart;
        if (more === 0 && strstart === 0 && lookahead === 0) {
          more = w_size;
        } else if (more == -1) {
          more--;
        } else if (strstart >= w_size + w_size - MIN_LOOKAHEAD) {
          win.set(win.subarray(w_size, w_size + w_size), 0);
          match_start -= w_size;
          strstart -= w_size;
          block_start -= w_size;
          n = hash_size;
          p = n;
          do {
            m = head[--p] & 65535;
            head[p] = m >= w_size ? m - w_size : 0;
          } while (--n !== 0);
          n = w_size;
          p = n;
          do {
            m = prev[--p] & 65535;
            prev[p] = m >= w_size ? m - w_size : 0;
          } while (--n !== 0);
          more += w_size;
        }
        if (strm.avail_in === 0)
          return;
        n = strm.read_buf(win, strstart + lookahead, more);
        lookahead += n;
        if (lookahead >= MIN_MATCH) {
          ins_h = win[strstart] & 255;
          ins_h = (ins_h << hash_shift ^ win[strstart + 1] & 255) & hash_mask;
        }
      } while (lookahead < MIN_LOOKAHEAD && strm.avail_in !== 0);
    }
    function deflate_stored2(flush) {
      let max_block_size = 65535;
      let max_start;
      if (max_block_size > pending_buf_size - 5) {
        max_block_size = pending_buf_size - 5;
      }
      while (true) {
        if (lookahead <= 1) {
          fill_window2();
          if (lookahead === 0 && flush == Z_NO_FLUSH)
            return NeedMore;
          if (lookahead === 0)
            break;
        }
        strstart += lookahead;
        lookahead = 0;
        max_start = block_start + max_block_size;
        if (strstart === 0 || strstart >= max_start) {
          lookahead = strstart - max_start;
          strstart = max_start;
          flush_block_only2(false);
          if (strm.avail_out === 0)
            return NeedMore;
        }
        if (strstart - block_start >= w_size - MIN_LOOKAHEAD) {
          flush_block_only2(false);
          if (strm.avail_out === 0)
            return NeedMore;
        }
      }
      flush_block_only2(flush == Z_FINISH);
      if (strm.avail_out === 0)
        return flush == Z_FINISH ? FinishStarted : NeedMore;
      return flush == Z_FINISH ? FinishDone : BlockDone;
    }
    function longest_match2(cur_match) {
      let chain_length = max_chain_length;
      let scan = strstart;
      let match;
      let len;
      let best_len = prev_length;
      const limit = strstart > w_size - MIN_LOOKAHEAD ? strstart - (w_size - MIN_LOOKAHEAD) : 0;
      let _nice_match = nice_match;
      const wmask = w_mask;
      const strend = strstart + MAX_MATCH;
      let scan_end1 = win[scan + best_len - 1];
      let scan_end = win[scan + best_len];
      if (prev_length >= good_match) {
        chain_length >>= 2;
      }
      if (_nice_match > lookahead)
        _nice_match = lookahead;
      do {
        match = cur_match;
        if (win[match + best_len] != scan_end || win[match + best_len - 1] != scan_end1 || win[match] != win[scan] || win[++match] != win[scan + 1])
          continue;
        scan += 2;
        match++;
        do {
        } while (win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && scan < strend);
        len = MAX_MATCH - (strend - scan);
        scan = strend - MAX_MATCH;
        if (len > best_len) {
          match_start = cur_match;
          best_len = len;
          if (len >= _nice_match)
            break;
          scan_end1 = win[scan + best_len - 1];
          scan_end = win[scan + best_len];
        }
      } while ((cur_match = prev[cur_match & wmask] & 65535) > limit && --chain_length !== 0);
      if (best_len <= lookahead)
        return best_len;
      return lookahead;
    }
    function deflate_fast2(flush) {
      let hash_head = 0;
      let bflush;
      while (true) {
        if (lookahead < MIN_LOOKAHEAD) {
          fill_window2();
          if (lookahead < MIN_LOOKAHEAD && flush == Z_NO_FLUSH) {
            return NeedMore;
          }
          if (lookahead === 0)
            break;
        }
        if (lookahead >= MIN_MATCH) {
          ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
          hash_head = head[ins_h] & 65535;
          prev[strstart & w_mask] = head[ins_h];
          head[ins_h] = strstart;
        }
        if (hash_head !== 0 && (strstart - hash_head & 65535) <= w_size - MIN_LOOKAHEAD) {
          if (strategy != Z_HUFFMAN_ONLY) {
            match_length = longest_match2(hash_head);
          }
        }
        if (match_length >= MIN_MATCH) {
          bflush = _tr_tally2(strstart - match_start, match_length - MIN_MATCH);
          lookahead -= match_length;
          if (match_length <= max_lazy_match && lookahead >= MIN_MATCH) {
            match_length--;
            do {
              strstart++;
              ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
              hash_head = head[ins_h] & 65535;
              prev[strstart & w_mask] = head[ins_h];
              head[ins_h] = strstart;
            } while (--match_length !== 0);
            strstart++;
          } else {
            strstart += match_length;
            match_length = 0;
            ins_h = win[strstart] & 255;
            ins_h = (ins_h << hash_shift ^ win[strstart + 1] & 255) & hash_mask;
          }
        } else {
          bflush = _tr_tally2(0, win[strstart] & 255);
          lookahead--;
          strstart++;
        }
        if (bflush) {
          flush_block_only2(false);
          if (strm.avail_out === 0)
            return NeedMore;
        }
      }
      flush_block_only2(flush == Z_FINISH);
      if (strm.avail_out === 0) {
        if (flush == Z_FINISH)
          return FinishStarted;
        else
          return NeedMore;
      }
      return flush == Z_FINISH ? FinishDone : BlockDone;
    }
    function deflate_slow2(flush) {
      let hash_head = 0;
      let bflush;
      let max_insert;
      while (true) {
        if (lookahead < MIN_LOOKAHEAD) {
          fill_window2();
          if (lookahead < MIN_LOOKAHEAD && flush == Z_NO_FLUSH) {
            return NeedMore;
          }
          if (lookahead === 0)
            break;
        }
        if (lookahead >= MIN_MATCH) {
          ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
          hash_head = head[ins_h] & 65535;
          prev[strstart & w_mask] = head[ins_h];
          head[ins_h] = strstart;
        }
        prev_length = match_length;
        prev_match = match_start;
        match_length = MIN_MATCH - 1;
        if (hash_head !== 0 && prev_length < max_lazy_match && (strstart - hash_head & 65535) <= w_size - MIN_LOOKAHEAD) {
          if (strategy != Z_HUFFMAN_ONLY) {
            match_length = longest_match2(hash_head);
          }
          if (match_length <= 5 && (strategy == Z_FILTERED || match_length == MIN_MATCH && strstart - match_start > 4096)) {
            match_length = MIN_MATCH - 1;
          }
        }
        if (prev_length >= MIN_MATCH && match_length <= prev_length) {
          max_insert = strstart + lookahead - MIN_MATCH;
          bflush = _tr_tally2(strstart - 1 - prev_match, prev_length - MIN_MATCH);
          lookahead -= prev_length - 1;
          prev_length -= 2;
          do {
            if (++strstart <= max_insert) {
              ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
              hash_head = head[ins_h] & 65535;
              prev[strstart & w_mask] = head[ins_h];
              head[ins_h] = strstart;
            }
          } while (--prev_length !== 0);
          match_available = 0;
          match_length = MIN_MATCH - 1;
          strstart++;
          if (bflush) {
            flush_block_only2(false);
            if (strm.avail_out === 0)
              return NeedMore;
          }
        } else if (match_available !== 0) {
          bflush = _tr_tally2(0, win[strstart - 1] & 255);
          if (bflush) {
            flush_block_only2(false);
          }
          strstart++;
          lookahead--;
          if (strm.avail_out === 0)
            return NeedMore;
        } else {
          match_available = 1;
          strstart++;
          lookahead--;
        }
      }
      if (match_available !== 0) {
        bflush = _tr_tally2(0, win[strstart - 1] & 255);
        match_available = 0;
      }
      flush_block_only2(flush == Z_FINISH);
      if (strm.avail_out === 0) {
        if (flush == Z_FINISH)
          return FinishStarted;
        else
          return NeedMore;
      }
      return flush == Z_FINISH ? FinishDone : BlockDone;
    }
    function deflateReset2(strm2) {
      strm2.total_in = strm2.total_out = 0;
      strm2.msg = null;
      that.pending = 0;
      that.pending_out = 0;
      status = BUSY_STATE;
      last_flush = Z_NO_FLUSH;
      tr_init();
      lm_init2();
      return Z_OK;
    }
    that.deflateInit = function(strm2, _level, bits, _method, memLevel, _strategy) {
      if (!_method)
        _method = Z_DEFLATED;
      if (!memLevel)
        memLevel = DEF_MEM_LEVEL;
      if (!_strategy)
        _strategy = Z_DEFAULT_STRATEGY;
      strm2.msg = null;
      if (_level == Z_DEFAULT_COMPRESSION)
        _level = 6;
      if (memLevel < 1 || memLevel > MAX_MEM_LEVEL || _method != Z_DEFLATED || bits < 9 || bits > 15 || _level < 0 || _level > 9 || _strategy < 0 || _strategy > Z_HUFFMAN_ONLY) {
        return Z_STREAM_ERROR;
      }
      strm2.dstate = that;
      w_bits = bits;
      w_size = 1 << w_bits;
      w_mask = w_size - 1;
      hash_bits = memLevel + 7;
      hash_size = 1 << hash_bits;
      hash_mask = hash_size - 1;
      hash_shift = Math.floor((hash_bits + MIN_MATCH - 1) / MIN_MATCH);
      win = new Uint8Array(w_size * 2);
      prev = [];
      head = [];
      lit_bufsize = 1 << memLevel + 6;
      that.pending_buf = new Uint8Array(lit_bufsize * 4);
      pending_buf_size = lit_bufsize * 4;
      that.dist_buf = new Uint16Array(lit_bufsize);
      that.lc_buf = new Uint8Array(lit_bufsize);
      level = _level;
      strategy = _strategy;
      return deflateReset2(strm2);
    };
    that.deflateEnd = function() {
      if (status != INIT_STATE && status != BUSY_STATE && status != FINISH_STATE) {
        return Z_STREAM_ERROR;
      }
      that.lc_buf = null;
      that.dist_buf = null;
      that.pending_buf = null;
      head = null;
      prev = null;
      win = null;
      that.dstate = null;
      return status == BUSY_STATE ? Z_DATA_ERROR : Z_OK;
    };
    that.deflateParams = function(strm2, _level, _strategy) {
      let err2 = Z_OK;
      if (_level == Z_DEFAULT_COMPRESSION) {
        _level = 6;
      }
      if (_level < 0 || _level > 9 || _strategy < 0 || _strategy > Z_HUFFMAN_ONLY) {
        return Z_STREAM_ERROR;
      }
      if (config_table[level].func != config_table[_level].func && strm2.total_in !== 0) {
        err2 = strm2.deflate(Z_PARTIAL_FLUSH);
      }
      if (level != _level) {
        level = _level;
        max_lazy_match = config_table[level].max_lazy;
        good_match = config_table[level].good_length;
        nice_match = config_table[level].nice_length;
        max_chain_length = config_table[level].max_chain;
      }
      strategy = _strategy;
      return err2;
    };
    that.deflateSetDictionary = function(_strm, dictionary, dictLength) {
      let length = dictLength;
      let n, index = 0;
      if (!dictionary || status != INIT_STATE)
        return Z_STREAM_ERROR;
      if (length < MIN_MATCH)
        return Z_OK;
      if (length > w_size - MIN_LOOKAHEAD) {
        length = w_size - MIN_LOOKAHEAD;
        index = dictLength - length;
      }
      win.set(dictionary.subarray(index, index + length), 0);
      strstart = length;
      block_start = length;
      ins_h = win[0] & 255;
      ins_h = (ins_h << hash_shift ^ win[1] & 255) & hash_mask;
      for (n = 0; n <= length - MIN_MATCH; n++) {
        ins_h = (ins_h << hash_shift ^ win[n + (MIN_MATCH - 1)] & 255) & hash_mask;
        prev[n & w_mask] = head[ins_h];
        head[ins_h] = n;
      }
      return Z_OK;
    };
    that.deflate = function(_strm, flush) {
      let i, header, level_flags, old_flush, bstate;
      if (flush > Z_FINISH || flush < 0) {
        return Z_STREAM_ERROR;
      }
      if (!_strm.next_out || !_strm.next_in && _strm.avail_in !== 0 || status == FINISH_STATE && flush != Z_FINISH) {
        _strm.msg = z_errmsg[Z_NEED_DICT - Z_STREAM_ERROR];
        return Z_STREAM_ERROR;
      }
      if (_strm.avail_out === 0) {
        _strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
        return Z_BUF_ERROR;
      }
      strm = _strm;
      old_flush = last_flush;
      last_flush = flush;
      if (status == INIT_STATE) {
        header = Z_DEFLATED + (w_bits - 8 << 4) << 8;
        level_flags = (level - 1 & 255) >> 1;
        if (level_flags > 3)
          level_flags = 3;
        header |= level_flags << 6;
        if (strstart !== 0)
          header |= PRESET_DICT;
        header += 31 - header % 31;
        status = BUSY_STATE;
        putShortMSB2(header);
      }
      if (that.pending !== 0) {
        strm.flush_pending();
        if (strm.avail_out === 0) {
          last_flush = -1;
          return Z_OK;
        }
      } else if (strm.avail_in === 0 && flush <= old_flush && flush != Z_FINISH) {
        strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
        return Z_BUF_ERROR;
      }
      if (status == FINISH_STATE && strm.avail_in !== 0) {
        _strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
        return Z_BUF_ERROR;
      }
      if (strm.avail_in !== 0 || lookahead !== 0 || flush != Z_NO_FLUSH && status != FINISH_STATE) {
        bstate = -1;
        switch (config_table[level].func) {
          case STORED:
            bstate = deflate_stored2(flush);
            break;
          case FAST:
            bstate = deflate_fast2(flush);
            break;
          case SLOW:
            bstate = deflate_slow2(flush);
            break;
          default:
        }
        if (bstate == FinishStarted || bstate == FinishDone) {
          status = FINISH_STATE;
        }
        if (bstate == NeedMore || bstate == FinishStarted) {
          if (strm.avail_out === 0) {
            last_flush = -1;
          }
          return Z_OK;
        }
        if (bstate == BlockDone) {
          if (flush == Z_PARTIAL_FLUSH) {
            _tr_align2();
          } else {
            _tr_stored_block2(0, 0, false);
            if (flush == Z_FULL_FLUSH) {
              for (i = 0; i < hash_size; i++)
                head[i] = 0;
            }
          }
          strm.flush_pending();
          if (strm.avail_out === 0) {
            last_flush = -1;
            return Z_OK;
          }
        }
      }
      if (flush != Z_FINISH)
        return Z_OK;
      return Z_STREAM_END;
    };
  }
  function ZStream() {
    const that = this;
    that.next_in_index = 0;
    that.next_out_index = 0;
    that.avail_in = 0;
    that.total_in = 0;
    that.avail_out = 0;
    that.total_out = 0;
  }
  ZStream.prototype = {
    deflateInit(level, bits) {
      const that = this;
      that.dstate = new Deflate();
      if (!bits)
        bits = MAX_BITS;
      return that.dstate.deflateInit(that, level, bits);
    },
    deflate(flush) {
      const that = this;
      if (!that.dstate) {
        return Z_STREAM_ERROR;
      }
      return that.dstate.deflate(that, flush);
    },
    deflateEnd() {
      const that = this;
      if (!that.dstate)
        return Z_STREAM_ERROR;
      const ret = that.dstate.deflateEnd();
      that.dstate = null;
      return ret;
    },
    deflateParams(level, strategy) {
      const that = this;
      if (!that.dstate)
        return Z_STREAM_ERROR;
      return that.dstate.deflateParams(that, level, strategy);
    },
    deflateSetDictionary(dictionary, dictLength) {
      const that = this;
      if (!that.dstate)
        return Z_STREAM_ERROR;
      return that.dstate.deflateSetDictionary(that, dictionary, dictLength);
    },
    // Read a new buffer from the current input stream, update the
    // total number of bytes read. All deflate() input goes through
    // this function so some applications may wish to modify it to avoid
    // allocating a large strm->next_in buffer and copying from it.
    // (See also flush_pending()).
    read_buf(buf, start, size) {
      const that = this;
      let len = that.avail_in;
      if (len > size)
        len = size;
      if (len === 0)
        return 0;
      that.avail_in -= len;
      buf.set(that.next_in.subarray(that.next_in_index, that.next_in_index + len), start);
      that.next_in_index += len;
      that.total_in += len;
      return len;
    },
    // Flush as much pending output as possible. All deflate() output goes
    // through this function so some applications may wish to modify it
    // to avoid allocating a large strm->next_out buffer and copying into it.
    // (See also read_buf()).
    flush_pending() {
      const that = this;
      let len = that.dstate.pending;
      if (len > that.avail_out)
        len = that.avail_out;
      if (len === 0)
        return;
      that.next_out.set(that.dstate.pending_buf.subarray(that.dstate.pending_out, that.dstate.pending_out + len), that.next_out_index);
      that.next_out_index += len;
      that.dstate.pending_out += len;
      that.total_out += len;
      that.avail_out -= len;
      that.dstate.pending -= len;
      if (that.dstate.pending === 0) {
        that.dstate.pending_out = 0;
      }
    }
  };
  function ZipDeflate(options) {
    const that = this;
    const z = new ZStream();
    const bufsize = getMaximumCompressedSize(options && options.chunkSize ? options.chunkSize : 64 * 1024);
    const flush = Z_NO_FLUSH;
    const buf = new Uint8Array(bufsize);
    let level = options ? options.level : Z_DEFAULT_COMPRESSION;
    if (typeof level == "undefined")
      level = Z_DEFAULT_COMPRESSION;
    z.deflateInit(level);
    z.next_out = buf;
    that.append = function(data, onprogress) {
      let err2, array, lastIndex = 0, bufferIndex = 0, bufferSize = 0;
      const buffers = [];
      if (!data.length)
        return;
      z.next_in_index = 0;
      z.next_in = data;
      z.avail_in = data.length;
      do {
        z.next_out_index = 0;
        z.avail_out = bufsize;
        err2 = z.deflate(flush);
        if (err2 != Z_OK)
          throw new Error("deflating: " + z.msg);
        if (z.next_out_index)
          if (z.next_out_index == bufsize)
            buffers.push(new Uint8Array(buf));
          else
            buffers.push(buf.subarray(0, z.next_out_index));
        bufferSize += z.next_out_index;
        if (onprogress && z.next_in_index > 0 && z.next_in_index != lastIndex) {
          onprogress(z.next_in_index);
          lastIndex = z.next_in_index;
        }
      } while (z.avail_in > 0 || z.avail_out === 0);
      if (buffers.length > 1) {
        array = new Uint8Array(bufferSize);
        buffers.forEach(function(chunk) {
          array.set(chunk, bufferIndex);
          bufferIndex += chunk.length;
        });
      } else {
        array = buffers[0] ? new Uint8Array(buffers[0]) : new Uint8Array();
      }
      return array;
    };
    that.flush = function() {
      let err2, array, bufferIndex = 0, bufferSize = 0;
      const buffers = [];
      do {
        z.next_out_index = 0;
        z.avail_out = bufsize;
        err2 = z.deflate(Z_FINISH);
        if (err2 != Z_STREAM_END && err2 != Z_OK)
          throw new Error("deflating: " + z.msg);
        if (bufsize - z.avail_out > 0)
          buffers.push(buf.slice(0, z.next_out_index));
        bufferSize += z.next_out_index;
      } while (z.avail_in > 0 || z.avail_out === 0);
      z.deflateEnd();
      array = new Uint8Array(bufferSize);
      buffers.forEach(function(chunk) {
        array.set(chunk, bufferIndex);
        bufferIndex += chunk.length;
      });
      return array;
    };
  }
  function getMaximumCompressedSize(uncompressedSize) {
    return uncompressedSize + 5 * (Math.floor(uncompressedSize / 16383) + 1);
  }

  // lib/zipjs/lib/core/streams/codecs/inflate.js
  var MAX_BITS2 = 15;
  var Z_OK2 = 0;
  var Z_STREAM_END2 = 1;
  var Z_NEED_DICT2 = 2;
  var Z_STREAM_ERROR2 = -2;
  var Z_DATA_ERROR2 = -3;
  var Z_MEM_ERROR = -4;
  var Z_BUF_ERROR2 = -5;
  var inflate_mask = [
    0,
    1,
    3,
    7,
    15,
    31,
    63,
    127,
    255,
    511,
    1023,
    2047,
    4095,
    8191,
    16383,
    32767,
    65535
  ];
  var MANY = 1440;
  var Z_NO_FLUSH2 = 0;
  var Z_FINISH2 = 4;
  var fixed_bl = 9;
  var fixed_bd = 5;
  var fixed_tl = [
    96,
    7,
    256,
    0,
    8,
    80,
    0,
    8,
    16,
    84,
    8,
    115,
    82,
    7,
    31,
    0,
    8,
    112,
    0,
    8,
    48,
    0,
    9,
    192,
    80,
    7,
    10,
    0,
    8,
    96,
    0,
    8,
    32,
    0,
    9,
    160,
    0,
    8,
    0,
    0,
    8,
    128,
    0,
    8,
    64,
    0,
    9,
    224,
    80,
    7,
    6,
    0,
    8,
    88,
    0,
    8,
    24,
    0,
    9,
    144,
    83,
    7,
    59,
    0,
    8,
    120,
    0,
    8,
    56,
    0,
    9,
    208,
    81,
    7,
    17,
    0,
    8,
    104,
    0,
    8,
    40,
    0,
    9,
    176,
    0,
    8,
    8,
    0,
    8,
    136,
    0,
    8,
    72,
    0,
    9,
    240,
    80,
    7,
    4,
    0,
    8,
    84,
    0,
    8,
    20,
    85,
    8,
    227,
    83,
    7,
    43,
    0,
    8,
    116,
    0,
    8,
    52,
    0,
    9,
    200,
    81,
    7,
    13,
    0,
    8,
    100,
    0,
    8,
    36,
    0,
    9,
    168,
    0,
    8,
    4,
    0,
    8,
    132,
    0,
    8,
    68,
    0,
    9,
    232,
    80,
    7,
    8,
    0,
    8,
    92,
    0,
    8,
    28,
    0,
    9,
    152,
    84,
    7,
    83,
    0,
    8,
    124,
    0,
    8,
    60,
    0,
    9,
    216,
    82,
    7,
    23,
    0,
    8,
    108,
    0,
    8,
    44,
    0,
    9,
    184,
    0,
    8,
    12,
    0,
    8,
    140,
    0,
    8,
    76,
    0,
    9,
    248,
    80,
    7,
    3,
    0,
    8,
    82,
    0,
    8,
    18,
    85,
    8,
    163,
    83,
    7,
    35,
    0,
    8,
    114,
    0,
    8,
    50,
    0,
    9,
    196,
    81,
    7,
    11,
    0,
    8,
    98,
    0,
    8,
    34,
    0,
    9,
    164,
    0,
    8,
    2,
    0,
    8,
    130,
    0,
    8,
    66,
    0,
    9,
    228,
    80,
    7,
    7,
    0,
    8,
    90,
    0,
    8,
    26,
    0,
    9,
    148,
    84,
    7,
    67,
    0,
    8,
    122,
    0,
    8,
    58,
    0,
    9,
    212,
    82,
    7,
    19,
    0,
    8,
    106,
    0,
    8,
    42,
    0,
    9,
    180,
    0,
    8,
    10,
    0,
    8,
    138,
    0,
    8,
    74,
    0,
    9,
    244,
    80,
    7,
    5,
    0,
    8,
    86,
    0,
    8,
    22,
    192,
    8,
    0,
    83,
    7,
    51,
    0,
    8,
    118,
    0,
    8,
    54,
    0,
    9,
    204,
    81,
    7,
    15,
    0,
    8,
    102,
    0,
    8,
    38,
    0,
    9,
    172,
    0,
    8,
    6,
    0,
    8,
    134,
    0,
    8,
    70,
    0,
    9,
    236,
    80,
    7,
    9,
    0,
    8,
    94,
    0,
    8,
    30,
    0,
    9,
    156,
    84,
    7,
    99,
    0,
    8,
    126,
    0,
    8,
    62,
    0,
    9,
    220,
    82,
    7,
    27,
    0,
    8,
    110,
    0,
    8,
    46,
    0,
    9,
    188,
    0,
    8,
    14,
    0,
    8,
    142,
    0,
    8,
    78,
    0,
    9,
    252,
    96,
    7,
    256,
    0,
    8,
    81,
    0,
    8,
    17,
    85,
    8,
    131,
    82,
    7,
    31,
    0,
    8,
    113,
    0,
    8,
    49,
    0,
    9,
    194,
    80,
    7,
    10,
    0,
    8,
    97,
    0,
    8,
    33,
    0,
    9,
    162,
    0,
    8,
    1,
    0,
    8,
    129,
    0,
    8,
    65,
    0,
    9,
    226,
    80,
    7,
    6,
    0,
    8,
    89,
    0,
    8,
    25,
    0,
    9,
    146,
    83,
    7,
    59,
    0,
    8,
    121,
    0,
    8,
    57,
    0,
    9,
    210,
    81,
    7,
    17,
    0,
    8,
    105,
    0,
    8,
    41,
    0,
    9,
    178,
    0,
    8,
    9,
    0,
    8,
    137,
    0,
    8,
    73,
    0,
    9,
    242,
    80,
    7,
    4,
    0,
    8,
    85,
    0,
    8,
    21,
    80,
    8,
    258,
    83,
    7,
    43,
    0,
    8,
    117,
    0,
    8,
    53,
    0,
    9,
    202,
    81,
    7,
    13,
    0,
    8,
    101,
    0,
    8,
    37,
    0,
    9,
    170,
    0,
    8,
    5,
    0,
    8,
    133,
    0,
    8,
    69,
    0,
    9,
    234,
    80,
    7,
    8,
    0,
    8,
    93,
    0,
    8,
    29,
    0,
    9,
    154,
    84,
    7,
    83,
    0,
    8,
    125,
    0,
    8,
    61,
    0,
    9,
    218,
    82,
    7,
    23,
    0,
    8,
    109,
    0,
    8,
    45,
    0,
    9,
    186,
    0,
    8,
    13,
    0,
    8,
    141,
    0,
    8,
    77,
    0,
    9,
    250,
    80,
    7,
    3,
    0,
    8,
    83,
    0,
    8,
    19,
    85,
    8,
    195,
    83,
    7,
    35,
    0,
    8,
    115,
    0,
    8,
    51,
    0,
    9,
    198,
    81,
    7,
    11,
    0,
    8,
    99,
    0,
    8,
    35,
    0,
    9,
    166,
    0,
    8,
    3,
    0,
    8,
    131,
    0,
    8,
    67,
    0,
    9,
    230,
    80,
    7,
    7,
    0,
    8,
    91,
    0,
    8,
    27,
    0,
    9,
    150,
    84,
    7,
    67,
    0,
    8,
    123,
    0,
    8,
    59,
    0,
    9,
    214,
    82,
    7,
    19,
    0,
    8,
    107,
    0,
    8,
    43,
    0,
    9,
    182,
    0,
    8,
    11,
    0,
    8,
    139,
    0,
    8,
    75,
    0,
    9,
    246,
    80,
    7,
    5,
    0,
    8,
    87,
    0,
    8,
    23,
    192,
    8,
    0,
    83,
    7,
    51,
    0,
    8,
    119,
    0,
    8,
    55,
    0,
    9,
    206,
    81,
    7,
    15,
    0,
    8,
    103,
    0,
    8,
    39,
    0,
    9,
    174,
    0,
    8,
    7,
    0,
    8,
    135,
    0,
    8,
    71,
    0,
    9,
    238,
    80,
    7,
    9,
    0,
    8,
    95,
    0,
    8,
    31,
    0,
    9,
    158,
    84,
    7,
    99,
    0,
    8,
    127,
    0,
    8,
    63,
    0,
    9,
    222,
    82,
    7,
    27,
    0,
    8,
    111,
    0,
    8,
    47,
    0,
    9,
    190,
    0,
    8,
    15,
    0,
    8,
    143,
    0,
    8,
    79,
    0,
    9,
    254,
    96,
    7,
    256,
    0,
    8,
    80,
    0,
    8,
    16,
    84,
    8,
    115,
    82,
    7,
    31,
    0,
    8,
    112,
    0,
    8,
    48,
    0,
    9,
    193,
    80,
    7,
    10,
    0,
    8,
    96,
    0,
    8,
    32,
    0,
    9,
    161,
    0,
    8,
    0,
    0,
    8,
    128,
    0,
    8,
    64,
    0,
    9,
    225,
    80,
    7,
    6,
    0,
    8,
    88,
    0,
    8,
    24,
    0,
    9,
    145,
    83,
    7,
    59,
    0,
    8,
    120,
    0,
    8,
    56,
    0,
    9,
    209,
    81,
    7,
    17,
    0,
    8,
    104,
    0,
    8,
    40,
    0,
    9,
    177,
    0,
    8,
    8,
    0,
    8,
    136,
    0,
    8,
    72,
    0,
    9,
    241,
    80,
    7,
    4,
    0,
    8,
    84,
    0,
    8,
    20,
    85,
    8,
    227,
    83,
    7,
    43,
    0,
    8,
    116,
    0,
    8,
    52,
    0,
    9,
    201,
    81,
    7,
    13,
    0,
    8,
    100,
    0,
    8,
    36,
    0,
    9,
    169,
    0,
    8,
    4,
    0,
    8,
    132,
    0,
    8,
    68,
    0,
    9,
    233,
    80,
    7,
    8,
    0,
    8,
    92,
    0,
    8,
    28,
    0,
    9,
    153,
    84,
    7,
    83,
    0,
    8,
    124,
    0,
    8,
    60,
    0,
    9,
    217,
    82,
    7,
    23,
    0,
    8,
    108,
    0,
    8,
    44,
    0,
    9,
    185,
    0,
    8,
    12,
    0,
    8,
    140,
    0,
    8,
    76,
    0,
    9,
    249,
    80,
    7,
    3,
    0,
    8,
    82,
    0,
    8,
    18,
    85,
    8,
    163,
    83,
    7,
    35,
    0,
    8,
    114,
    0,
    8,
    50,
    0,
    9,
    197,
    81,
    7,
    11,
    0,
    8,
    98,
    0,
    8,
    34,
    0,
    9,
    165,
    0,
    8,
    2,
    0,
    8,
    130,
    0,
    8,
    66,
    0,
    9,
    229,
    80,
    7,
    7,
    0,
    8,
    90,
    0,
    8,
    26,
    0,
    9,
    149,
    84,
    7,
    67,
    0,
    8,
    122,
    0,
    8,
    58,
    0,
    9,
    213,
    82,
    7,
    19,
    0,
    8,
    106,
    0,
    8,
    42,
    0,
    9,
    181,
    0,
    8,
    10,
    0,
    8,
    138,
    0,
    8,
    74,
    0,
    9,
    245,
    80,
    7,
    5,
    0,
    8,
    86,
    0,
    8,
    22,
    192,
    8,
    0,
    83,
    7,
    51,
    0,
    8,
    118,
    0,
    8,
    54,
    0,
    9,
    205,
    81,
    7,
    15,
    0,
    8,
    102,
    0,
    8,
    38,
    0,
    9,
    173,
    0,
    8,
    6,
    0,
    8,
    134,
    0,
    8,
    70,
    0,
    9,
    237,
    80,
    7,
    9,
    0,
    8,
    94,
    0,
    8,
    30,
    0,
    9,
    157,
    84,
    7,
    99,
    0,
    8,
    126,
    0,
    8,
    62,
    0,
    9,
    221,
    82,
    7,
    27,
    0,
    8,
    110,
    0,
    8,
    46,
    0,
    9,
    189,
    0,
    8,
    14,
    0,
    8,
    142,
    0,
    8,
    78,
    0,
    9,
    253,
    96,
    7,
    256,
    0,
    8,
    81,
    0,
    8,
    17,
    85,
    8,
    131,
    82,
    7,
    31,
    0,
    8,
    113,
    0,
    8,
    49,
    0,
    9,
    195,
    80,
    7,
    10,
    0,
    8,
    97,
    0,
    8,
    33,
    0,
    9,
    163,
    0,
    8,
    1,
    0,
    8,
    129,
    0,
    8,
    65,
    0,
    9,
    227,
    80,
    7,
    6,
    0,
    8,
    89,
    0,
    8,
    25,
    0,
    9,
    147,
    83,
    7,
    59,
    0,
    8,
    121,
    0,
    8,
    57,
    0,
    9,
    211,
    81,
    7,
    17,
    0,
    8,
    105,
    0,
    8,
    41,
    0,
    9,
    179,
    0,
    8,
    9,
    0,
    8,
    137,
    0,
    8,
    73,
    0,
    9,
    243,
    80,
    7,
    4,
    0,
    8,
    85,
    0,
    8,
    21,
    80,
    8,
    258,
    83,
    7,
    43,
    0,
    8,
    117,
    0,
    8,
    53,
    0,
    9,
    203,
    81,
    7,
    13,
    0,
    8,
    101,
    0,
    8,
    37,
    0,
    9,
    171,
    0,
    8,
    5,
    0,
    8,
    133,
    0,
    8,
    69,
    0,
    9,
    235,
    80,
    7,
    8,
    0,
    8,
    93,
    0,
    8,
    29,
    0,
    9,
    155,
    84,
    7,
    83,
    0,
    8,
    125,
    0,
    8,
    61,
    0,
    9,
    219,
    82,
    7,
    23,
    0,
    8,
    109,
    0,
    8,
    45,
    0,
    9,
    187,
    0,
    8,
    13,
    0,
    8,
    141,
    0,
    8,
    77,
    0,
    9,
    251,
    80,
    7,
    3,
    0,
    8,
    83,
    0,
    8,
    19,
    85,
    8,
    195,
    83,
    7,
    35,
    0,
    8,
    115,
    0,
    8,
    51,
    0,
    9,
    199,
    81,
    7,
    11,
    0,
    8,
    99,
    0,
    8,
    35,
    0,
    9,
    167,
    0,
    8,
    3,
    0,
    8,
    131,
    0,
    8,
    67,
    0,
    9,
    231,
    80,
    7,
    7,
    0,
    8,
    91,
    0,
    8,
    27,
    0,
    9,
    151,
    84,
    7,
    67,
    0,
    8,
    123,
    0,
    8,
    59,
    0,
    9,
    215,
    82,
    7,
    19,
    0,
    8,
    107,
    0,
    8,
    43,
    0,
    9,
    183,
    0,
    8,
    11,
    0,
    8,
    139,
    0,
    8,
    75,
    0,
    9,
    247,
    80,
    7,
    5,
    0,
    8,
    87,
    0,
    8,
    23,
    192,
    8,
    0,
    83,
    7,
    51,
    0,
    8,
    119,
    0,
    8,
    55,
    0,
    9,
    207,
    81,
    7,
    15,
    0,
    8,
    103,
    0,
    8,
    39,
    0,
    9,
    175,
    0,
    8,
    7,
    0,
    8,
    135,
    0,
    8,
    71,
    0,
    9,
    239,
    80,
    7,
    9,
    0,
    8,
    95,
    0,
    8,
    31,
    0,
    9,
    159,
    84,
    7,
    99,
    0,
    8,
    127,
    0,
    8,
    63,
    0,
    9,
    223,
    82,
    7,
    27,
    0,
    8,
    111,
    0,
    8,
    47,
    0,
    9,
    191,
    0,
    8,
    15,
    0,
    8,
    143,
    0,
    8,
    79,
    0,
    9,
    255
  ];
  var fixed_td = [
    80,
    5,
    1,
    87,
    5,
    257,
    83,
    5,
    17,
    91,
    5,
    4097,
    81,
    5,
    5,
    89,
    5,
    1025,
    85,
    5,
    65,
    93,
    5,
    16385,
    80,
    5,
    3,
    88,
    5,
    513,
    84,
    5,
    33,
    92,
    5,
    8193,
    82,
    5,
    9,
    90,
    5,
    2049,
    86,
    5,
    129,
    192,
    5,
    24577,
    80,
    5,
    2,
    87,
    5,
    385,
    83,
    5,
    25,
    91,
    5,
    6145,
    81,
    5,
    7,
    89,
    5,
    1537,
    85,
    5,
    97,
    93,
    5,
    24577,
    80,
    5,
    4,
    88,
    5,
    769,
    84,
    5,
    49,
    92,
    5,
    12289,
    82,
    5,
    13,
    90,
    5,
    3073,
    86,
    5,
    193,
    192,
    5,
    24577
  ];
  var cplens = [
    // Copy lengths for literal codes 257..285
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    13,
    15,
    17,
    19,
    23,
    27,
    31,
    35,
    43,
    51,
    59,
    67,
    83,
    99,
    115,
    131,
    163,
    195,
    227,
    258,
    0,
    0
  ];
  var cplext = [
    // Extra bits for literal codes 257..285
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    1,
    1,
    1,
    1,
    2,
    2,
    2,
    2,
    3,
    3,
    3,
    3,
    4,
    4,
    4,
    4,
    5,
    5,
    5,
    5,
    0,
    112,
    112
    // 112==invalid
  ];
  var cpdist = [
    // Copy offsets for distance codes 0..29
    1,
    2,
    3,
    4,
    5,
    7,
    9,
    13,
    17,
    25,
    33,
    49,
    65,
    97,
    129,
    193,
    257,
    385,
    513,
    769,
    1025,
    1537,
    2049,
    3073,
    4097,
    6145,
    8193,
    12289,
    16385,
    24577
  ];
  var cpdext = [
    // Extra bits for distance codes
    0,
    0,
    0,
    0,
    1,
    1,
    2,
    2,
    3,
    3,
    4,
    4,
    5,
    5,
    6,
    6,
    7,
    7,
    8,
    8,
    9,
    9,
    10,
    10,
    11,
    11,
    12,
    12,
    13,
    13
  ];
  var BMAX = 15;
  function InfTree() {
    const that = this;
    let hn;
    let v;
    let c;
    let r;
    let u;
    let x;
    function huft_build(b, bindex, n, s, d, e2, t, m, hp, hn2, v2) {
      let a;
      let f;
      let g;
      let h;
      let i;
      let j;
      let k;
      let l;
      let mask;
      let p;
      let q;
      let w;
      let xp;
      let y;
      let z;
      p = 0;
      i = n;
      do {
        c[b[bindex + p]]++;
        p++;
        i--;
      } while (i !== 0);
      if (c[0] == n) {
        t[0] = -1;
        m[0] = 0;
        return Z_OK2;
      }
      l = m[0];
      for (j = 1; j <= BMAX; j++)
        if (c[j] !== 0)
          break;
      k = j;
      if (l < j) {
        l = j;
      }
      for (i = BMAX; i !== 0; i--) {
        if (c[i] !== 0)
          break;
      }
      g = i;
      if (l > i) {
        l = i;
      }
      m[0] = l;
      for (y = 1 << j; j < i; j++, y <<= 1) {
        if ((y -= c[j]) < 0) {
          return Z_DATA_ERROR2;
        }
      }
      if ((y -= c[i]) < 0) {
        return Z_DATA_ERROR2;
      }
      c[i] += y;
      x[1] = j = 0;
      p = 1;
      xp = 2;
      while (--i !== 0) {
        x[xp] = j += c[p];
        xp++;
        p++;
      }
      i = 0;
      p = 0;
      do {
        if ((j = b[bindex + p]) !== 0) {
          v2[x[j]++] = i;
        }
        p++;
      } while (++i < n);
      n = x[g];
      x[0] = i = 0;
      p = 0;
      h = -1;
      w = -l;
      u[0] = 0;
      q = 0;
      z = 0;
      for (; k <= g; k++) {
        a = c[k];
        while (a-- !== 0) {
          while (k > w + l) {
            h++;
            w += l;
            z = g - w;
            z = z > l ? l : z;
            if ((f = 1 << (j = k - w)) > a + 1) {
              f -= a + 1;
              xp = k;
              if (j < z) {
                while (++j < z) {
                  if ((f <<= 1) <= c[++xp])
                    break;
                  f -= c[xp];
                }
              }
            }
            z = 1 << j;
            if (hn2[0] + z > MANY) {
              return Z_DATA_ERROR2;
            }
            u[h] = q = /* hp+ */
            hn2[0];
            hn2[0] += z;
            if (h !== 0) {
              x[h] = i;
              r[0] = /* (byte) */
              j;
              r[1] = /* (byte) */
              l;
              j = i >>> w - l;
              r[2] = /* (int) */
              q - u[h - 1] - j;
              hp.set(r, (u[h - 1] + j) * 3);
            } else {
              t[0] = q;
            }
          }
          r[1] = /* (byte) */
          k - w;
          if (p >= n) {
            r[0] = 128 + 64;
          } else if (v2[p] < s) {
            r[0] = /* (byte) */
            v2[p] < 256 ? 0 : 32 + 64;
            r[2] = v2[p++];
          } else {
            r[0] = /* (byte) */
            e2[v2[p] - s] + 16 + 64;
            r[2] = d[v2[p++] - s];
          }
          f = 1 << k - w;
          for (j = i >>> w; j < z; j += f) {
            hp.set(r, (q + j) * 3);
          }
          for (j = 1 << k - 1; (i & j) !== 0; j >>>= 1) {
            i ^= j;
          }
          i ^= j;
          mask = (1 << w) - 1;
          while ((i & mask) != x[h]) {
            h--;
            w -= l;
            mask = (1 << w) - 1;
          }
        }
      }
      return y !== 0 && g != 1 ? Z_BUF_ERROR2 : Z_OK2;
    }
    function initWorkArea(vsize) {
      let i;
      if (!hn) {
        hn = [];
        v = [];
        c = new Int32Array(BMAX + 1);
        r = [];
        u = new Int32Array(BMAX);
        x = new Int32Array(BMAX + 1);
      }
      if (v.length < vsize) {
        v = [];
      }
      for (i = 0; i < vsize; i++) {
        v[i] = 0;
      }
      for (i = 0; i < BMAX + 1; i++) {
        c[i] = 0;
      }
      for (i = 0; i < 3; i++) {
        r[i] = 0;
      }
      u.set(c.subarray(0, BMAX), 0);
      x.set(c.subarray(0, BMAX + 1), 0);
    }
    that.inflate_trees_bits = function(c2, bb, tb, hp, z) {
      let result;
      initWorkArea(19);
      hn[0] = 0;
      result = huft_build(c2, 0, 19, 19, null, null, tb, bb, hp, hn, v);
      if (result == Z_DATA_ERROR2) {
        z.msg = "oversubscribed dynamic bit lengths tree";
      } else if (result == Z_BUF_ERROR2 || bb[0] === 0) {
        z.msg = "incomplete dynamic bit lengths tree";
        result = Z_DATA_ERROR2;
      }
      return result;
    };
    that.inflate_trees_dynamic = function(nl, nd, c2, bl, bd, tl, td, hp, z) {
      let result;
      initWorkArea(288);
      hn[0] = 0;
      result = huft_build(c2, 0, nl, 257, cplens, cplext, tl, bl, hp, hn, v);
      if (result != Z_OK2 || bl[0] === 0) {
        if (result == Z_DATA_ERROR2) {
          z.msg = "oversubscribed literal/length tree";
        } else if (result != Z_MEM_ERROR) {
          z.msg = "incomplete literal/length tree";
          result = Z_DATA_ERROR2;
        }
        return result;
      }
      initWorkArea(288);
      result = huft_build(c2, nl, nd, 0, cpdist, cpdext, td, bd, hp, hn, v);
      if (result != Z_OK2 || bd[0] === 0 && nl > 257) {
        if (result == Z_DATA_ERROR2) {
          z.msg = "oversubscribed distance tree";
        } else if (result == Z_BUF_ERROR2) {
          z.msg = "incomplete distance tree";
          result = Z_DATA_ERROR2;
        } else if (result != Z_MEM_ERROR) {
          z.msg = "empty distance tree with lengths";
          result = Z_DATA_ERROR2;
        }
        return result;
      }
      return Z_OK2;
    };
  }
  InfTree.inflate_trees_fixed = function(bl, bd, tl, td) {
    bl[0] = fixed_bl;
    bd[0] = fixed_bd;
    tl[0] = fixed_tl;
    td[0] = fixed_td;
    return Z_OK2;
  };
  var START = 0;
  var LEN = 1;
  var LENEXT = 2;
  var DIST = 3;
  var DISTEXT = 4;
  var COPY = 5;
  var LIT = 6;
  var WASH = 7;
  var END = 8;
  var BADCODE = 9;
  function InfCodes() {
    const that = this;
    let mode2;
    let len = 0;
    let tree;
    let tree_index = 0;
    let need = 0;
    let lit = 0;
    let get = 0;
    let dist = 0;
    let lbits = 0;
    let dbits = 0;
    let ltree;
    let ltree_index = 0;
    let dtree;
    let dtree_index = 0;
    function inflate_fast2(bl, bd, tl, tl_index, td, td_index, s, z) {
      let t;
      let tp;
      let tp_index;
      let e2;
      let b;
      let k;
      let p;
      let n;
      let q;
      let m;
      let ml;
      let md;
      let c;
      let d;
      let r;
      let tp_index_t_3;
      p = z.next_in_index;
      n = z.avail_in;
      b = s.bitb;
      k = s.bitk;
      q = s.write;
      m = q < s.read ? s.read - q - 1 : s.end - q;
      ml = inflate_mask[bl];
      md = inflate_mask[bd];
      do {
        while (k < 20) {
          n--;
          b |= (z.read_byte(p++) & 255) << k;
          k += 8;
        }
        t = b & ml;
        tp = tl;
        tp_index = tl_index;
        tp_index_t_3 = (tp_index + t) * 3;
        if ((e2 = tp[tp_index_t_3]) === 0) {
          b >>= tp[tp_index_t_3 + 1];
          k -= tp[tp_index_t_3 + 1];
          s.win[q++] = /* (byte) */
          tp[tp_index_t_3 + 2];
          m--;
          continue;
        }
        do {
          b >>= tp[tp_index_t_3 + 1];
          k -= tp[tp_index_t_3 + 1];
          if ((e2 & 16) !== 0) {
            e2 &= 15;
            c = tp[tp_index_t_3 + 2] + /* (int) */
            (b & inflate_mask[e2]);
            b >>= e2;
            k -= e2;
            while (k < 15) {
              n--;
              b |= (z.read_byte(p++) & 255) << k;
              k += 8;
            }
            t = b & md;
            tp = td;
            tp_index = td_index;
            tp_index_t_3 = (tp_index + t) * 3;
            e2 = tp[tp_index_t_3];
            do {
              b >>= tp[tp_index_t_3 + 1];
              k -= tp[tp_index_t_3 + 1];
              if ((e2 & 16) !== 0) {
                e2 &= 15;
                while (k < e2) {
                  n--;
                  b |= (z.read_byte(p++) & 255) << k;
                  k += 8;
                }
                d = tp[tp_index_t_3 + 2] + (b & inflate_mask[e2]);
                b >>= e2;
                k -= e2;
                m -= c;
                if (q >= d) {
                  r = q - d;
                  if (q - r > 0 && 2 > q - r) {
                    s.win[q++] = s.win[r++];
                    s.win[q++] = s.win[r++];
                    c -= 2;
                  } else {
                    s.win.set(s.win.subarray(r, r + 2), q);
                    q += 2;
                    r += 2;
                    c -= 2;
                  }
                } else {
                  r = q - d;
                  do {
                    r += s.end;
                  } while (r < 0);
                  e2 = s.end - r;
                  if (c > e2) {
                    c -= e2;
                    if (q - r > 0 && e2 > q - r) {
                      do {
                        s.win[q++] = s.win[r++];
                      } while (--e2 !== 0);
                    } else {
                      s.win.set(s.win.subarray(r, r + e2), q);
                      q += e2;
                      r += e2;
                      e2 = 0;
                    }
                    r = 0;
                  }
                }
                if (q - r > 0 && c > q - r) {
                  do {
                    s.win[q++] = s.win[r++];
                  } while (--c !== 0);
                } else {
                  s.win.set(s.win.subarray(r, r + c), q);
                  q += c;
                  r += c;
                  c = 0;
                }
                break;
              } else if ((e2 & 64) === 0) {
                t += tp[tp_index_t_3 + 2];
                t += b & inflate_mask[e2];
                tp_index_t_3 = (tp_index + t) * 3;
                e2 = tp[tp_index_t_3];
              } else {
                z.msg = "invalid distance code";
                c = z.avail_in - n;
                c = k >> 3 < c ? k >> 3 : c;
                n += c;
                p -= c;
                k -= c << 3;
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return Z_DATA_ERROR2;
              }
            } while (true);
            break;
          }
          if ((e2 & 64) === 0) {
            t += tp[tp_index_t_3 + 2];
            t += b & inflate_mask[e2];
            tp_index_t_3 = (tp_index + t) * 3;
            if ((e2 = tp[tp_index_t_3]) === 0) {
              b >>= tp[tp_index_t_3 + 1];
              k -= tp[tp_index_t_3 + 1];
              s.win[q++] = /* (byte) */
              tp[tp_index_t_3 + 2];
              m--;
              break;
            }
          } else if ((e2 & 32) !== 0) {
            c = z.avail_in - n;
            c = k >> 3 < c ? k >> 3 : c;
            n += c;
            p -= c;
            k -= c << 3;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return Z_STREAM_END2;
          } else {
            z.msg = "invalid literal/length code";
            c = z.avail_in - n;
            c = k >> 3 < c ? k >> 3 : c;
            n += c;
            p -= c;
            k -= c << 3;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return Z_DATA_ERROR2;
          }
        } while (true);
      } while (m >= 258 && n >= 10);
      c = z.avail_in - n;
      c = k >> 3 < c ? k >> 3 : c;
      n += c;
      p -= c;
      k -= c << 3;
      s.bitb = b;
      s.bitk = k;
      z.avail_in = n;
      z.total_in += p - z.next_in_index;
      z.next_in_index = p;
      s.write = q;
      return Z_OK2;
    }
    that.init = function(bl, bd, tl, tl_index, td, td_index) {
      mode2 = START;
      lbits = /* (byte) */
      bl;
      dbits = /* (byte) */
      bd;
      ltree = tl;
      ltree_index = tl_index;
      dtree = td;
      dtree_index = td_index;
      tree = null;
    };
    that.proc = function(s, z, r) {
      let j;
      let tindex;
      let e2;
      let b = 0;
      let k = 0;
      let p = 0;
      let n;
      let q;
      let m;
      let f;
      p = z.next_in_index;
      n = z.avail_in;
      b = s.bitb;
      k = s.bitk;
      q = s.write;
      m = q < s.read ? s.read - q - 1 : s.end - q;
      while (true) {
        switch (mode2) {
          // waiting for "i:"=input, "o:"=output, "x:"=nothing
          case START:
            if (m >= 258 && n >= 10) {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              r = inflate_fast2(lbits, dbits, ltree, ltree_index, dtree, dtree_index, s, z);
              p = z.next_in_index;
              n = z.avail_in;
              b = s.bitb;
              k = s.bitk;
              q = s.write;
              m = q < s.read ? s.read - q - 1 : s.end - q;
              if (r != Z_OK2) {
                mode2 = r == Z_STREAM_END2 ? WASH : BADCODE;
                break;
              }
            }
            need = lbits;
            tree = ltree;
            tree_index = ltree_index;
            mode2 = LEN;
          /* falls through */
          case LEN:
            j = need;
            while (k < j) {
              if (n !== 0)
                r = Z_OK2;
              else {
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return s.inflate_flush(z, r);
              }
              n--;
              b |= (z.read_byte(p++) & 255) << k;
              k += 8;
            }
            tindex = (tree_index + (b & inflate_mask[j])) * 3;
            b >>>= tree[tindex + 1];
            k -= tree[tindex + 1];
            e2 = tree[tindex];
            if (e2 === 0) {
              lit = tree[tindex + 2];
              mode2 = LIT;
              break;
            }
            if ((e2 & 16) !== 0) {
              get = e2 & 15;
              len = tree[tindex + 2];
              mode2 = LENEXT;
              break;
            }
            if ((e2 & 64) === 0) {
              need = e2;
              tree_index = tindex / 3 + tree[tindex + 2];
              break;
            }
            if ((e2 & 32) !== 0) {
              mode2 = WASH;
              break;
            }
            mode2 = BADCODE;
            z.msg = "invalid literal/length code";
            r = Z_DATA_ERROR2;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
          case LENEXT:
            j = get;
            while (k < j) {
              if (n !== 0)
                r = Z_OK2;
              else {
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return s.inflate_flush(z, r);
              }
              n--;
              b |= (z.read_byte(p++) & 255) << k;
              k += 8;
            }
            len += b & inflate_mask[j];
            b >>= j;
            k -= j;
            need = dbits;
            tree = dtree;
            tree_index = dtree_index;
            mode2 = DIST;
          /* falls through */
          case DIST:
            j = need;
            while (k < j) {
              if (n !== 0)
                r = Z_OK2;
              else {
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return s.inflate_flush(z, r);
              }
              n--;
              b |= (z.read_byte(p++) & 255) << k;
              k += 8;
            }
            tindex = (tree_index + (b & inflate_mask[j])) * 3;
            b >>= tree[tindex + 1];
            k -= tree[tindex + 1];
            e2 = tree[tindex];
            if ((e2 & 16) !== 0) {
              get = e2 & 15;
              dist = tree[tindex + 2];
              mode2 = DISTEXT;
              break;
            }
            if ((e2 & 64) === 0) {
              need = e2;
              tree_index = tindex / 3 + tree[tindex + 2];
              break;
            }
            mode2 = BADCODE;
            z.msg = "invalid distance code";
            r = Z_DATA_ERROR2;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
          case DISTEXT:
            j = get;
            while (k < j) {
              if (n !== 0)
                r = Z_OK2;
              else {
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return s.inflate_flush(z, r);
              }
              n--;
              b |= (z.read_byte(p++) & 255) << k;
              k += 8;
            }
            dist += b & inflate_mask[j];
            b >>= j;
            k -= j;
            mode2 = COPY;
          /* falls through */
          case COPY:
            f = q - dist;
            while (f < 0) {
              f += s.end;
            }
            while (len !== 0) {
              if (m === 0) {
                if (q == s.end && s.read !== 0) {
                  q = 0;
                  m = q < s.read ? s.read - q - 1 : s.end - q;
                }
                if (m === 0) {
                  s.write = q;
                  r = s.inflate_flush(z, r);
                  q = s.write;
                  m = q < s.read ? s.read - q - 1 : s.end - q;
                  if (q == s.end && s.read !== 0) {
                    q = 0;
                    m = q < s.read ? s.read - q - 1 : s.end - q;
                  }
                  if (m === 0) {
                    s.bitb = b;
                    s.bitk = k;
                    z.avail_in = n;
                    z.total_in += p - z.next_in_index;
                    z.next_in_index = p;
                    s.write = q;
                    return s.inflate_flush(z, r);
                  }
                }
              }
              s.win[q++] = s.win[f++];
              m--;
              if (f == s.end)
                f = 0;
              len--;
            }
            mode2 = START;
            break;
          case LIT:
            if (m === 0) {
              if (q == s.end && s.read !== 0) {
                q = 0;
                m = q < s.read ? s.read - q - 1 : s.end - q;
              }
              if (m === 0) {
                s.write = q;
                r = s.inflate_flush(z, r);
                q = s.write;
                m = q < s.read ? s.read - q - 1 : s.end - q;
                if (q == s.end && s.read !== 0) {
                  q = 0;
                  m = q < s.read ? s.read - q - 1 : s.end - q;
                }
                if (m === 0) {
                  s.bitb = b;
                  s.bitk = k;
                  z.avail_in = n;
                  z.total_in += p - z.next_in_index;
                  z.next_in_index = p;
                  s.write = q;
                  return s.inflate_flush(z, r);
                }
              }
            }
            r = Z_OK2;
            s.win[q++] = /* (byte) */
            lit;
            m--;
            mode2 = START;
            break;
          case WASH:
            if (k > 7) {
              k -= 8;
              n++;
              p--;
            }
            s.write = q;
            r = s.inflate_flush(z, r);
            q = s.write;
            m = q < s.read ? s.read - q - 1 : s.end - q;
            if (s.read != s.write) {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return s.inflate_flush(z, r);
            }
            mode2 = END;
          /* falls through */
          case END:
            r = Z_STREAM_END2;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
          case BADCODE:
            r = Z_DATA_ERROR2;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
          default:
            r = Z_STREAM_ERROR2;
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
        }
      }
    };
    that.free = function() {
    };
  }
  var border = [
    // Order of the bit length code lengths
    16,
    17,
    18,
    0,
    8,
    7,
    9,
    6,
    10,
    5,
    11,
    4,
    12,
    3,
    13,
    2,
    14,
    1,
    15
  ];
  var TYPE = 0;
  var LENS = 1;
  var STORED2 = 2;
  var TABLE = 3;
  var BTREE = 4;
  var DTREE = 5;
  var CODES = 6;
  var DRY = 7;
  var DONELOCKS = 8;
  var BADBLOCKS = 9;
  function InfBlocks(z, w) {
    const that = this;
    let mode2 = TYPE;
    let left = 0;
    let table3 = 0;
    let index = 0;
    let blens;
    const bb = [0];
    const tb = [0];
    const codes = new InfCodes();
    let last = 0;
    let hufts = new Int32Array(MANY * 3);
    const check = 0;
    const inftree = new InfTree();
    that.bitk = 0;
    that.bitb = 0;
    that.win = new Uint8Array(w);
    that.end = w;
    that.read = 0;
    that.write = 0;
    that.reset = function(z2, c) {
      if (c)
        c[0] = check;
      if (mode2 == CODES) {
        codes.free(z2);
      }
      mode2 = TYPE;
      that.bitk = 0;
      that.bitb = 0;
      that.read = that.write = 0;
    };
    that.reset(z, null);
    that.inflate_flush = function(z2, r) {
      let n;
      let p;
      let q;
      p = z2.next_out_index;
      q = that.read;
      n = /* (int) */
      (q <= that.write ? that.write : that.end) - q;
      if (n > z2.avail_out)
        n = z2.avail_out;
      if (n !== 0 && r == Z_BUF_ERROR2)
        r = Z_OK2;
      z2.avail_out -= n;
      z2.total_out += n;
      z2.next_out.set(that.win.subarray(q, q + n), p);
      p += n;
      q += n;
      if (q == that.end) {
        q = 0;
        if (that.write == that.end)
          that.write = 0;
        n = that.write - q;
        if (n > z2.avail_out)
          n = z2.avail_out;
        if (n !== 0 && r == Z_BUF_ERROR2)
          r = Z_OK2;
        z2.avail_out -= n;
        z2.total_out += n;
        z2.next_out.set(that.win.subarray(q, q + n), p);
        p += n;
        q += n;
      }
      z2.next_out_index = p;
      that.read = q;
      return r;
    };
    that.proc = function(z2, r) {
      let t;
      let b;
      let k;
      let p;
      let n;
      let q;
      let m;
      let i;
      p = z2.next_in_index;
      n = z2.avail_in;
      b = that.bitb;
      k = that.bitk;
      q = that.write;
      m = /* (int) */
      q < that.read ? that.read - q - 1 : that.end - q;
      while (true) {
        let bl, bd, tl, td, bl_, bd_, tl_, td_;
        switch (mode2) {
          case TYPE:
            while (k < 3) {
              if (n !== 0) {
                r = Z_OK2;
              } else {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              n--;
              b |= (z2.read_byte(p++) & 255) << k;
              k += 8;
            }
            t = /* (int) */
            b & 7;
            last = t & 1;
            switch (t >>> 1) {
              case 0:
                b >>>= 3;
                k -= 3;
                t = k & 7;
                b >>>= t;
                k -= t;
                mode2 = LENS;
                break;
              case 1:
                bl = [];
                bd = [];
                tl = [[]];
                td = [[]];
                InfTree.inflate_trees_fixed(bl, bd, tl, td);
                codes.init(bl[0], bd[0], tl[0], 0, td[0], 0);
                b >>>= 3;
                k -= 3;
                mode2 = CODES;
                break;
              case 2:
                b >>>= 3;
                k -= 3;
                mode2 = TABLE;
                break;
              case 3:
                b >>>= 3;
                k -= 3;
                mode2 = BADBLOCKS;
                z2.msg = "invalid block type";
                r = Z_DATA_ERROR2;
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
            }
            break;
          case LENS:
            while (k < 32) {
              if (n !== 0) {
                r = Z_OK2;
              } else {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              n--;
              b |= (z2.read_byte(p++) & 255) << k;
              k += 8;
            }
            if ((~b >>> 16 & 65535) != (b & 65535)) {
              mode2 = BADBLOCKS;
              z2.msg = "invalid stored block lengths";
              r = Z_DATA_ERROR2;
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            left = b & 65535;
            b = k = 0;
            mode2 = left !== 0 ? STORED2 : last !== 0 ? DRY : TYPE;
            break;
          case STORED2:
            if (n === 0) {
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            if (m === 0) {
              if (q == that.end && that.read !== 0) {
                q = 0;
                m = /* (int) */
                q < that.read ? that.read - q - 1 : that.end - q;
              }
              if (m === 0) {
                that.write = q;
                r = that.inflate_flush(z2, r);
                q = that.write;
                m = /* (int) */
                q < that.read ? that.read - q - 1 : that.end - q;
                if (q == that.end && that.read !== 0) {
                  q = 0;
                  m = /* (int) */
                  q < that.read ? that.read - q - 1 : that.end - q;
                }
                if (m === 0) {
                  that.bitb = b;
                  that.bitk = k;
                  z2.avail_in = n;
                  z2.total_in += p - z2.next_in_index;
                  z2.next_in_index = p;
                  that.write = q;
                  return that.inflate_flush(z2, r);
                }
              }
            }
            r = Z_OK2;
            t = left;
            if (t > n)
              t = n;
            if (t > m)
              t = m;
            that.win.set(z2.read_buf(p, t), q);
            p += t;
            n -= t;
            q += t;
            m -= t;
            if ((left -= t) !== 0)
              break;
            mode2 = last !== 0 ? DRY : TYPE;
            break;
          case TABLE:
            while (k < 14) {
              if (n !== 0) {
                r = Z_OK2;
              } else {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              n--;
              b |= (z2.read_byte(p++) & 255) << k;
              k += 8;
            }
            table3 = t = b & 16383;
            if ((t & 31) > 29 || (t >> 5 & 31) > 29) {
              mode2 = BADBLOCKS;
              z2.msg = "too many length or distance symbols";
              r = Z_DATA_ERROR2;
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            t = 258 + (t & 31) + (t >> 5 & 31);
            if (!blens || blens.length < t) {
              blens = [];
            } else {
              for (i = 0; i < t; i++) {
                blens[i] = 0;
              }
            }
            b >>>= 14;
            k -= 14;
            index = 0;
            mode2 = BTREE;
          /* falls through */
          case BTREE:
            while (index < 4 + (table3 >>> 10)) {
              while (k < 3) {
                if (n !== 0) {
                  r = Z_OK2;
                } else {
                  that.bitb = b;
                  that.bitk = k;
                  z2.avail_in = n;
                  z2.total_in += p - z2.next_in_index;
                  z2.next_in_index = p;
                  that.write = q;
                  return that.inflate_flush(z2, r);
                }
                n--;
                b |= (z2.read_byte(p++) & 255) << k;
                k += 8;
              }
              blens[border[index++]] = b & 7;
              b >>>= 3;
              k -= 3;
            }
            while (index < 19) {
              blens[border[index++]] = 0;
            }
            bb[0] = 7;
            t = inftree.inflate_trees_bits(blens, bb, tb, hufts, z2);
            if (t != Z_OK2) {
              r = t;
              if (r == Z_DATA_ERROR2) {
                blens = null;
                mode2 = BADBLOCKS;
              }
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            index = 0;
            mode2 = DTREE;
          /* falls through */
          case DTREE:
            while (true) {
              t = table3;
              if (index >= 258 + (t & 31) + (t >> 5 & 31)) {
                break;
              }
              let j, c;
              t = bb[0];
              while (k < t) {
                if (n !== 0) {
                  r = Z_OK2;
                } else {
                  that.bitb = b;
                  that.bitk = k;
                  z2.avail_in = n;
                  z2.total_in += p - z2.next_in_index;
                  z2.next_in_index = p;
                  that.write = q;
                  return that.inflate_flush(z2, r);
                }
                n--;
                b |= (z2.read_byte(p++) & 255) << k;
                k += 8;
              }
              t = hufts[(tb[0] + (b & inflate_mask[t])) * 3 + 1];
              c = hufts[(tb[0] + (b & inflate_mask[t])) * 3 + 2];
              if (c < 16) {
                b >>>= t;
                k -= t;
                blens[index++] = c;
              } else {
                i = c == 18 ? 7 : c - 14;
                j = c == 18 ? 11 : 3;
                while (k < t + i) {
                  if (n !== 0) {
                    r = Z_OK2;
                  } else {
                    that.bitb = b;
                    that.bitk = k;
                    z2.avail_in = n;
                    z2.total_in += p - z2.next_in_index;
                    z2.next_in_index = p;
                    that.write = q;
                    return that.inflate_flush(z2, r);
                  }
                  n--;
                  b |= (z2.read_byte(p++) & 255) << k;
                  k += 8;
                }
                b >>>= t;
                k -= t;
                j += b & inflate_mask[i];
                b >>>= i;
                k -= i;
                i = index;
                t = table3;
                if (i + j > 258 + (t & 31) + (t >> 5 & 31) || c == 16 && i < 1) {
                  blens = null;
                  mode2 = BADBLOCKS;
                  z2.msg = "invalid bit length repeat";
                  r = Z_DATA_ERROR2;
                  that.bitb = b;
                  that.bitk = k;
                  z2.avail_in = n;
                  z2.total_in += p - z2.next_in_index;
                  z2.next_in_index = p;
                  that.write = q;
                  return that.inflate_flush(z2, r);
                }
                c = c == 16 ? blens[i - 1] : 0;
                do {
                  blens[i++] = c;
                } while (--j !== 0);
                index = i;
              }
            }
            tb[0] = -1;
            bl_ = [];
            bd_ = [];
            tl_ = [];
            td_ = [];
            bl_[0] = 9;
            bd_[0] = 6;
            t = table3;
            t = inftree.inflate_trees_dynamic(257 + (t & 31), 1 + (t >> 5 & 31), blens, bl_, bd_, tl_, td_, hufts, z2);
            if (t != Z_OK2) {
              if (t == Z_DATA_ERROR2) {
                blens = null;
                mode2 = BADBLOCKS;
              }
              r = t;
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            codes.init(bl_[0], bd_[0], hufts, tl_[0], hufts, td_[0]);
            mode2 = CODES;
          /* falls through */
          case CODES:
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            if ((r = codes.proc(that, z2, r)) != Z_STREAM_END2) {
              return that.inflate_flush(z2, r);
            }
            r = Z_OK2;
            codes.free(z2);
            p = z2.next_in_index;
            n = z2.avail_in;
            b = that.bitb;
            k = that.bitk;
            q = that.write;
            m = /* (int) */
            q < that.read ? that.read - q - 1 : that.end - q;
            if (last === 0) {
              mode2 = TYPE;
              break;
            }
            mode2 = DRY;
          /* falls through */
          case DRY:
            that.write = q;
            r = that.inflate_flush(z2, r);
            q = that.write;
            m = /* (int) */
            q < that.read ? that.read - q - 1 : that.end - q;
            if (that.read != that.write) {
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            mode2 = DONELOCKS;
          /* falls through */
          case DONELOCKS:
            r = Z_STREAM_END2;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          case BADBLOCKS:
            r = Z_DATA_ERROR2;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          default:
            r = Z_STREAM_ERROR2;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
        }
      }
    };
    that.free = function(z2) {
      that.reset(z2, null);
      that.win = null;
      hufts = null;
    };
    that.set_dictionary = function(d, start, n) {
      that.win.set(d.subarray(start, start + n), 0);
      that.read = that.write = n;
    };
    that.sync_point = function() {
      return mode2 == LENS ? 1 : 0;
    };
  }
  var PRESET_DICT2 = 32;
  var Z_DEFLATED2 = 8;
  var METHOD = 0;
  var FLAG = 1;
  var DICT4 = 2;
  var DICT3 = 3;
  var DICT2 = 4;
  var DICT1 = 5;
  var DICT0 = 6;
  var BLOCKS = 7;
  var DONE = 12;
  var BAD = 13;
  var mark = [0, 0, 255, 255];
  function Inflate() {
    const that = this;
    that.mode = 0;
    that.method = 0;
    that.was = [0];
    that.need = 0;
    that.marker = 0;
    that.wbits = 0;
    function inflateReset3(z) {
      if (!z || !z.istate)
        return Z_STREAM_ERROR2;
      z.total_in = z.total_out = 0;
      z.msg = null;
      z.istate.mode = BLOCKS;
      z.istate.blocks.reset(z, null);
      return Z_OK2;
    }
    that.inflateEnd = function(z) {
      if (that.blocks)
        that.blocks.free(z);
      that.blocks = null;
      return Z_OK2;
    };
    that.inflateInit = function(z, w) {
      z.msg = null;
      that.blocks = null;
      if (w < 8 || w > 15) {
        that.inflateEnd(z);
        return Z_STREAM_ERROR2;
      }
      that.wbits = w;
      z.istate.blocks = new InfBlocks(z, 1 << w);
      inflateReset3(z);
      return Z_OK2;
    };
    that.inflate = function(z, f) {
      let r;
      let b;
      if (!z || !z.istate || !z.next_in)
        return Z_STREAM_ERROR2;
      const istate = z.istate;
      f = f == Z_FINISH2 ? Z_BUF_ERROR2 : Z_OK2;
      r = Z_BUF_ERROR2;
      while (true) {
        switch (istate.mode) {
          case METHOD:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            if (((istate.method = z.read_byte(z.next_in_index++)) & 15) != Z_DEFLATED2) {
              istate.mode = BAD;
              z.msg = "unknown compression method";
              istate.marker = 5;
              break;
            }
            if ((istate.method >> 4) + 8 > istate.wbits) {
              istate.mode = BAD;
              z.msg = "invalid win size";
              istate.marker = 5;
              break;
            }
            istate.mode = FLAG;
          /* falls through */
          case FLAG:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            b = z.read_byte(z.next_in_index++) & 255;
            if (((istate.method << 8) + b) % 31 !== 0) {
              istate.mode = BAD;
              z.msg = "incorrect header check";
              istate.marker = 5;
              break;
            }
            if ((b & PRESET_DICT2) === 0) {
              istate.mode = BLOCKS;
              break;
            }
            istate.mode = DICT4;
          /* falls through */
          case DICT4:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            istate.need = (z.read_byte(z.next_in_index++) & 255) << 24 & 4278190080;
            istate.mode = DICT3;
          /* falls through */
          case DICT3:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            istate.need += (z.read_byte(z.next_in_index++) & 255) << 16 & 16711680;
            istate.mode = DICT2;
          /* falls through */
          case DICT2:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            istate.need += (z.read_byte(z.next_in_index++) & 255) << 8 & 65280;
            istate.mode = DICT1;
          /* falls through */
          case DICT1:
            if (z.avail_in === 0)
              return r;
            r = f;
            z.avail_in--;
            z.total_in++;
            istate.need += z.read_byte(z.next_in_index++) & 255;
            istate.mode = DICT0;
            return Z_NEED_DICT2;
          case DICT0:
            istate.mode = BAD;
            z.msg = "need dictionary";
            istate.marker = 0;
            return Z_STREAM_ERROR2;
          case BLOCKS:
            r = istate.blocks.proc(z, r);
            if (r == Z_DATA_ERROR2) {
              istate.mode = BAD;
              istate.marker = 0;
              break;
            }
            if (r == Z_OK2) {
              r = f;
            }
            if (r != Z_STREAM_END2) {
              return r;
            }
            r = f;
            istate.blocks.reset(z, istate.was);
            istate.mode = DONE;
          /* falls through */
          case DONE:
            z.avail_in = 0;
            return Z_STREAM_END2;
          case BAD:
            return Z_DATA_ERROR2;
          default:
            return Z_STREAM_ERROR2;
        }
      }
    };
    that.inflateSetDictionary = function(z, dictionary, dictLength) {
      let index = 0, length = dictLength;
      if (!z || !z.istate || z.istate.mode != DICT0)
        return Z_STREAM_ERROR2;
      const istate = z.istate;
      if (length >= 1 << istate.wbits) {
        length = (1 << istate.wbits) - 1;
        index = dictLength - length;
      }
      istate.blocks.set_dictionary(dictionary, index, length);
      istate.mode = BLOCKS;
      return Z_OK2;
    };
    that.inflateSync = function(z) {
      let n;
      let p;
      let m;
      let r, w;
      if (!z || !z.istate)
        return Z_STREAM_ERROR2;
      const istate = z.istate;
      if (istate.mode != BAD) {
        istate.mode = BAD;
        istate.marker = 0;
      }
      if ((n = z.avail_in) === 0)
        return Z_BUF_ERROR2;
      p = z.next_in_index;
      m = istate.marker;
      while (n !== 0 && m < 4) {
        if (z.read_byte(p) == mark[m]) {
          m++;
        } else if (z.read_byte(p) !== 0) {
          m = 0;
        } else {
          m = 4 - m;
        }
        p++;
        n--;
      }
      z.total_in += p - z.next_in_index;
      z.next_in_index = p;
      z.avail_in = n;
      istate.marker = m;
      if (m != 4) {
        return Z_DATA_ERROR2;
      }
      r = z.total_in;
      w = z.total_out;
      inflateReset3(z);
      z.total_in = r;
      z.total_out = w;
      istate.mode = BLOCKS;
      return Z_OK2;
    };
    that.inflateSyncPoint = function(z) {
      if (!z || !z.istate || !z.istate.blocks)
        return Z_STREAM_ERROR2;
      return z.istate.blocks.sync_point();
    };
  }
  function ZStream2() {
  }
  ZStream2.prototype = {
    inflateInit(bits) {
      const that = this;
      that.istate = new Inflate();
      if (!bits)
        bits = MAX_BITS2;
      return that.istate.inflateInit(that, bits);
    },
    inflate(f) {
      const that = this;
      if (!that.istate)
        return Z_STREAM_ERROR2;
      return that.istate.inflate(that, f);
    },
    inflateEnd() {
      const that = this;
      if (!that.istate)
        return Z_STREAM_ERROR2;
      const ret = that.istate.inflateEnd(that);
      that.istate = null;
      return ret;
    },
    inflateSync() {
      const that = this;
      if (!that.istate)
        return Z_STREAM_ERROR2;
      return that.istate.inflateSync(that);
    },
    inflateSetDictionary(dictionary, dictLength) {
      const that = this;
      if (!that.istate)
        return Z_STREAM_ERROR2;
      return that.istate.inflateSetDictionary(that, dictionary, dictLength);
    },
    read_byte(start) {
      const that = this;
      return that.next_in[start];
    },
    read_buf(start, size) {
      const that = this;
      return that.next_in.subarray(start, start + size);
    }
  };
  function ZipInflate(options) {
    const that = this;
    const z = new ZStream2();
    const bufsize = options && options.chunkSize ? Math.floor(options.chunkSize * 2) : 128 * 1024;
    const flush = Z_NO_FLUSH2;
    const buf = new Uint8Array(bufsize);
    let nomoreinput = false;
    z.inflateInit();
    z.next_out = buf;
    that.append = function(data, onprogress) {
      const buffers = [];
      let err2, array, lastIndex = 0, bufferIndex = 0, bufferSize = 0;
      if (data.length === 0)
        return;
      z.next_in_index = 0;
      z.next_in = data;
      z.avail_in = data.length;
      do {
        z.next_out_index = 0;
        z.avail_out = bufsize;
        if (z.avail_in === 0 && !nomoreinput) {
          z.next_in_index = 0;
          nomoreinput = true;
        }
        err2 = z.inflate(flush);
        if (nomoreinput && err2 === Z_BUF_ERROR2) {
          if (z.avail_in !== 0)
            throw new Error("inflating: bad input");
        } else if (err2 !== Z_OK2 && err2 !== Z_STREAM_END2)
          throw new Error("inflating: " + z.msg);
        if ((nomoreinput || err2 === Z_STREAM_END2) && z.avail_in === data.length)
          throw new Error("inflating: bad input");
        if (z.next_out_index)
          if (z.next_out_index === bufsize)
            buffers.push(new Uint8Array(buf));
          else
            buffers.push(buf.subarray(0, z.next_out_index));
        bufferSize += z.next_out_index;
        if (onprogress && z.next_in_index > 0 && z.next_in_index != lastIndex) {
          onprogress(z.next_in_index);
          lastIndex = z.next_in_index;
        }
      } while (z.avail_in > 0 || z.avail_out === 0);
      if (buffers.length > 1) {
        array = new Uint8Array(bufferSize);
        buffers.forEach(function(chunk) {
          array.set(chunk, bufferIndex);
          bufferIndex += chunk.length;
        });
      } else {
        array = buffers[0] ? new Uint8Array(buffers[0]) : new Uint8Array();
      }
      return array;
    };
    that.flush = function() {
      z.inflateEnd();
    };
  }

  // lib/zipjs/lib/core/constants.js
  var MAX_32_BITS = 4294967295;
  var MAX_16_BITS = 65535;
  var COMPRESSION_METHOD_DEFLATE = 8;
  var COMPRESSION_METHOD_STORE = 0;
  var COMPRESSION_METHOD_AES = 99;
  var LOCAL_FILE_HEADER_SIGNATURE = 67324752;
  var SPLIT_ZIP_FILE_SIGNATURE = 134695760;
  var CENTRAL_FILE_HEADER_SIGNATURE = 33639248;
  var END_OF_CENTRAL_DIR_SIGNATURE = 101010256;
  var ZIP64_END_OF_CENTRAL_DIR_SIGNATURE = 101075792;
  var ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIGNATURE = 117853008;
  var END_OF_CENTRAL_DIR_LENGTH = 22;
  var ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH = 20;
  var ZIP64_END_OF_CENTRAL_DIR_LENGTH = 56;
  var ZIP64_END_OF_CENTRAL_DIR_TOTAL_LENGTH = END_OF_CENTRAL_DIR_LENGTH + ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH + ZIP64_END_OF_CENTRAL_DIR_LENGTH;
  var EXTRAFIELD_TYPE_ZIP64 = 1;
  var EXTRAFIELD_TYPE_AES = 39169;
  var EXTRAFIELD_TYPE_NTFS = 10;
  var EXTRAFIELD_TYPE_NTFS_TAG1 = 1;
  var EXTRAFIELD_TYPE_EXTENDED_TIMESTAMP = 21589;
  var EXTRAFIELD_TYPE_UNICODE_PATH = 28789;
  var EXTRAFIELD_TYPE_UNICODE_COMMENT = 25461;
  var EXTRAFIELD_TYPE_USDZ = 6534;
  var BITFLAG_ENCRYPTED = 1;
  var BITFLAG_LEVEL = 6;
  var BITFLAG_DATA_DESCRIPTOR = 8;
  var BITFLAG_LANG_ENCODING_FLAG = 2048;
  var FILE_ATTR_MSDOS_DIR_MASK = 16;
  var DIRECTORY_SIGNATURE = "/";
  var MAX_DATE = new Date(2107, 11, 31);
  var MIN_DATE = new Date(1980, 0, 1);
  var UNDEFINED_VALUE = void 0;
  var UNDEFINED_TYPE = "undefined";
  var FUNCTION_TYPE = "function";

  // lib/zipjs/lib/core/streams/stream-adapter.js
  var StreamAdapter = class {
    constructor(Codec) {
      return class extends TransformStream {
        constructor(_format, options) {
          const codec2 = new Codec(options);
          super({
            transform(chunk, controller) {
              controller.enqueue(codec2.append(chunk));
            },
            flush(controller) {
              const chunk = codec2.flush();
              if (chunk) {
                controller.enqueue(chunk);
              }
            }
          });
        }
      };
    }
  };

  // lib/zipjs/lib/core/configuration.js
  var MINIMUM_CHUNK_SIZE = 64;
  var maxWorkers = 2;
  try {
    if (typeof navigator != UNDEFINED_TYPE && navigator.hardwareConcurrency) {
      maxWorkers = navigator.hardwareConcurrency;
    }
  } catch (_error) {
  }
  var DEFAULT_CONFIGURATION = {
    chunkSize: 512 * 1024,
    maxWorkers,
    terminateWorkerTimeout: 5e3,
    useWebWorkers: true,
    useCompressionStream: true,
    workerScripts: UNDEFINED_VALUE,
    CompressionStreamNative: typeof CompressionStream != UNDEFINED_TYPE && CompressionStream,
    DecompressionStreamNative: typeof DecompressionStream != UNDEFINED_TYPE && DecompressionStream
  };
  var config = Object.assign({}, DEFAULT_CONFIGURATION);
  function getConfiguration() {
    return config;
  }
  function getChunkSize(config3) {
    return Math.max(config3.chunkSize, MINIMUM_CHUNK_SIZE);
  }
  function configure(configuration) {
    const {
      baseURL: baseURL2,
      chunkSize,
      maxWorkers: maxWorkers2,
      terminateWorkerTimeout,
      useCompressionStream,
      useWebWorkers,
      Deflate: Deflate3,
      Inflate: Inflate3,
      CompressionStream: CompressionStream2,
      DecompressionStream: DecompressionStream2,
      workerScripts
    } = configuration;
    setIfDefined("baseURL", baseURL2);
    setIfDefined("chunkSize", chunkSize);
    setIfDefined("maxWorkers", maxWorkers2);
    setIfDefined("terminateWorkerTimeout", terminateWorkerTimeout);
    setIfDefined("useCompressionStream", useCompressionStream);
    setIfDefined("useWebWorkers", useWebWorkers);
    if (Deflate3) {
      config.CompressionStream = new StreamAdapter(Deflate3);
    }
    if (Inflate3) {
      config.DecompressionStream = new StreamAdapter(Inflate3);
    }
    setIfDefined("CompressionStream", CompressionStream2);
    setIfDefined("DecompressionStream", DecompressionStream2);
    if (workerScripts !== UNDEFINED_VALUE) {
      const { deflate: deflate2, inflate: inflate2 } = workerScripts;
      if (deflate2 || inflate2) {
        if (!config.workerScripts) {
          config.workerScripts = {};
        }
      }
      if (deflate2) {
        if (!Array.isArray(deflate2)) {
          throw new Error("workerScripts.deflate must be an array");
        }
        config.workerScripts.deflate = deflate2;
      }
      if (inflate2) {
        if (!Array.isArray(inflate2)) {
          throw new Error("workerScripts.inflate must be an array");
        }
        config.workerScripts.inflate = inflate2;
      }
    }
  }
  function setIfDefined(propertyName, propertyValue) {
    if (propertyValue !== UNDEFINED_VALUE) {
      config[propertyName] = propertyValue;
    }
  }

  // lib/zipjs/lib/core/util/mime-type.js
  var table = {
    "application": {
      "andrew-inset": "ez",
      "annodex": "anx",
      "atom+xml": "atom",
      "atomcat+xml": "atomcat",
      "atomserv+xml": "atomsrv",
      "bbolin": "lin",
      "cu-seeme": "cu",
      "davmount+xml": "davmount",
      "dsptype": "tsp",
      "ecmascript": [
        "es",
        "ecma"
      ],
      "futuresplash": "spl",
      "hta": "hta",
      "java-archive": "jar",
      "java-serialized-object": "ser",
      "java-vm": "class",
      "m3g": "m3g",
      "mac-binhex40": "hqx",
      "mathematica": [
        "nb",
        "ma",
        "mb"
      ],
      "msaccess": "mdb",
      "msword": [
        "doc",
        "dot",
        "wiz"
      ],
      "mxf": "mxf",
      "oda": "oda",
      "ogg": "ogx",
      "pdf": "pdf",
      "pgp-keys": "key",
      "pgp-signature": [
        "asc",
        "sig"
      ],
      "pics-rules": "prf",
      "postscript": [
        "ps",
        "ai",
        "eps",
        "epsi",
        "epsf",
        "eps2",
        "eps3"
      ],
      "rar": "rar",
      "rdf+xml": "rdf",
      "rss+xml": "rss",
      "rtf": "rtf",
      "xhtml+xml": [
        "xhtml",
        "xht"
      ],
      "xml": [
        "xml",
        "xsl",
        "xsd",
        "xpdl"
      ],
      "xspf+xml": "xspf",
      "zip": "zip",
      "vnd.android.package-archive": "apk",
      "vnd.cinderella": "cdy",
      "vnd.google-earth.kml+xml": "kml",
      "vnd.google-earth.kmz": "kmz",
      "vnd.mozilla.xul+xml": "xul",
      "vnd.ms-excel": [
        "xls",
        "xlb",
        "xlt",
        "xlm",
        "xla",
        "xlc",
        "xlw"
      ],
      "vnd.ms-pki.seccat": "cat",
      "vnd.ms-pki.stl": "stl",
      "vnd.ms-powerpoint": [
        "ppt",
        "pps",
        "pot",
        "ppa",
        "pwz"
      ],
      "vnd.oasis.opendocument.chart": "odc",
      "vnd.oasis.opendocument.database": "odb",
      "vnd.oasis.opendocument.formula": "odf",
      "vnd.oasis.opendocument.graphics": "odg",
      "vnd.oasis.opendocument.graphics-template": "otg",
      "vnd.oasis.opendocument.image": "odi",
      "vnd.oasis.opendocument.presentation": "odp",
      "vnd.oasis.opendocument.presentation-template": "otp",
      "vnd.oasis.opendocument.spreadsheet": "ods",
      "vnd.oasis.opendocument.spreadsheet-template": "ots",
      "vnd.oasis.opendocument.text": "odt",
      "vnd.oasis.opendocument.text-master": [
        "odm",
        "otm"
      ],
      "vnd.oasis.opendocument.text-template": "ott",
      "vnd.oasis.opendocument.text-web": "oth",
      "vnd.openxmlformats-officedocument.spreadsheetml.sheet": "xlsx",
      "vnd.openxmlformats-officedocument.spreadsheetml.template": "xltx",
      "vnd.openxmlformats-officedocument.presentationml.presentation": "pptx",
      "vnd.openxmlformats-officedocument.presentationml.slideshow": "ppsx",
      "vnd.openxmlformats-officedocument.presentationml.template": "potx",
      "vnd.openxmlformats-officedocument.wordprocessingml.document": "docx",
      "vnd.openxmlformats-officedocument.wordprocessingml.template": "dotx",
      "vnd.smaf": "mmf",
      "vnd.stardivision.calc": "sdc",
      "vnd.stardivision.chart": "sds",
      "vnd.stardivision.draw": "sda",
      "vnd.stardivision.impress": "sdd",
      "vnd.stardivision.math": [
        "sdf",
        "smf"
      ],
      "vnd.stardivision.writer": [
        "sdw",
        "vor"
      ],
      "vnd.stardivision.writer-global": "sgl",
      "vnd.sun.xml.calc": "sxc",
      "vnd.sun.xml.calc.template": "stc",
      "vnd.sun.xml.draw": "sxd",
      "vnd.sun.xml.draw.template": "std",
      "vnd.sun.xml.impress": "sxi",
      "vnd.sun.xml.impress.template": "sti",
      "vnd.sun.xml.math": "sxm",
      "vnd.sun.xml.writer": "sxw",
      "vnd.sun.xml.writer.global": "sxg",
      "vnd.sun.xml.writer.template": "stw",
      "vnd.symbian.install": [
        "sis",
        "sisx"
      ],
      "vnd.visio": [
        "vsd",
        "vst",
        "vss",
        "vsw",
        "vsdx",
        "vssx",
        "vstx",
        "vssm",
        "vstm"
      ],
      "vnd.wap.wbxml": "wbxml",
      "vnd.wap.wmlc": "wmlc",
      "vnd.wap.wmlscriptc": "wmlsc",
      "vnd.wordperfect": "wpd",
      "vnd.wordperfect5.1": "wp5",
      "x-123": "wk",
      "x-7z-compressed": "7z",
      "x-abiword": "abw",
      "x-apple-diskimage": "dmg",
      "x-bcpio": "bcpio",
      "x-bittorrent": "torrent",
      "x-cbr": [
        "cbr",
        "cba",
        "cbt",
        "cb7"
      ],
      "x-cbz": "cbz",
      "x-cdf": [
        "cdf",
        "cda"
      ],
      "x-cdlink": "vcd",
      "x-chess-pgn": "pgn",
      "x-cpio": "cpio",
      "x-csh": "csh",
      "x-director": [
        "dir",
        "dxr",
        "cst",
        "cct",
        "cxt",
        "w3d",
        "fgd",
        "swa"
      ],
      "x-dms": "dms",
      "x-doom": "wad",
      "x-dvi": "dvi",
      "x-httpd-eruby": "rhtml",
      "x-font": "pcf.Z",
      "x-freemind": "mm",
      "x-gnumeric": "gnumeric",
      "x-go-sgf": "sgf",
      "x-graphing-calculator": "gcf",
      "x-gtar": [
        "gtar",
        "taz"
      ],
      "x-hdf": "hdf",
      "x-httpd-php": [
        "phtml",
        "pht",
        "php"
      ],
      "x-httpd-php-source": "phps",
      "x-httpd-php3": "php3",
      "x-httpd-php3-preprocessed": "php3p",
      "x-httpd-php4": "php4",
      "x-httpd-php5": "php5",
      "x-ica": "ica",
      "x-info": "info",
      "x-internet-signup": [
        "ins",
        "isp"
      ],
      "x-iphone": "iii",
      "x-iso9660-image": "iso",
      "x-java-jnlp-file": "jnlp",
      "x-jmol": "jmz",
      "x-killustrator": "kil",
      "x-latex": "latex",
      "x-lyx": "lyx",
      "x-lzx": "lzx",
      "x-maker": [
        "frm",
        "fb",
        "fbdoc"
      ],
      "x-ms-wmd": "wmd",
      "x-msdos-program": [
        "com",
        "exe",
        "bat",
        "dll"
      ],
      "x-netcdf": [
        "nc"
      ],
      "x-ns-proxy-autoconfig": [
        "pac",
        "dat"
      ],
      "x-nwc": "nwc",
      "x-object": "o",
      "x-oz-application": "oza",
      "x-pkcs7-certreqresp": "p7r",
      "x-python-code": [
        "pyc",
        "pyo"
      ],
      "x-qgis": [
        "qgs",
        "shp",
        "shx"
      ],
      "x-quicktimeplayer": "qtl",
      "x-redhat-package-manager": [
        "rpm",
        "rpa"
      ],
      "x-ruby": "rb",
      "x-sh": "sh",
      "x-shar": "shar",
      "x-shockwave-flash": [
        "swf",
        "swfl"
      ],
      "x-silverlight": "scr",
      "x-stuffit": "sit",
      "x-sv4cpio": "sv4cpio",
      "x-sv4crc": "sv4crc",
      "x-tar": "tar",
      "x-tex-gf": "gf",
      "x-tex-pk": "pk",
      "x-texinfo": [
        "texinfo",
        "texi"
      ],
      "x-trash": [
        "~",
        "%",
        "bak",
        "old",
        "sik"
      ],
      "x-ustar": "ustar",
      "x-wais-source": "src",
      "x-wingz": "wz",
      "x-x509-ca-cert": [
        "crt",
        "der",
        "cer"
      ],
      "x-xcf": "xcf",
      "x-xfig": "fig",
      "x-xpinstall": "xpi",
      "applixware": "aw",
      "atomsvc+xml": "atomsvc",
      "ccxml+xml": "ccxml",
      "cdmi-capability": "cdmia",
      "cdmi-container": "cdmic",
      "cdmi-domain": "cdmid",
      "cdmi-object": "cdmio",
      "cdmi-queue": "cdmiq",
      "docbook+xml": "dbk",
      "dssc+der": "dssc",
      "dssc+xml": "xdssc",
      "emma+xml": "emma",
      "epub+zip": "epub",
      "exi": "exi",
      "font-tdpfr": "pfr",
      "gml+xml": "gml",
      "gpx+xml": "gpx",
      "gxf": "gxf",
      "hyperstudio": "stk",
      "inkml+xml": [
        "ink",
        "inkml"
      ],
      "ipfix": "ipfix",
      "jsonml+json": "jsonml",
      "lost+xml": "lostxml",
      "mads+xml": "mads",
      "marc": "mrc",
      "marcxml+xml": "mrcx",
      "mathml+xml": [
        "mathml",
        "mml"
      ],
      "mbox": "mbox",
      "mediaservercontrol+xml": "mscml",
      "metalink+xml": "metalink",
      "metalink4+xml": "meta4",
      "mets+xml": "mets",
      "mods+xml": "mods",
      "mp21": [
        "m21",
        "mp21"
      ],
      "mp4": "mp4s",
      "oebps-package+xml": "opf",
      "omdoc+xml": "omdoc",
      "onenote": [
        "onetoc",
        "onetoc2",
        "onetmp",
        "onepkg"
      ],
      "oxps": "oxps",
      "patch-ops-error+xml": "xer",
      "pgp-encrypted": "pgp",
      "pkcs10": "p10",
      "pkcs7-mime": [
        "p7m",
        "p7c"
      ],
      "pkcs7-signature": "p7s",
      "pkcs8": "p8",
      "pkix-attr-cert": "ac",
      "pkix-crl": "crl",
      "pkix-pkipath": "pkipath",
      "pkixcmp": "pki",
      "pls+xml": "pls",
      "prs.cww": "cww",
      "pskc+xml": "pskcxml",
      "reginfo+xml": "rif",
      "relax-ng-compact-syntax": "rnc",
      "resource-lists+xml": "rl",
      "resource-lists-diff+xml": "rld",
      "rls-services+xml": "rs",
      "rpki-ghostbusters": "gbr",
      "rpki-manifest": "mft",
      "rpki-roa": "roa",
      "rsd+xml": "rsd",
      "sbml+xml": "sbml",
      "scvp-cv-request": "scq",
      "scvp-cv-response": "scs",
      "scvp-vp-request": "spq",
      "scvp-vp-response": "spp",
      "sdp": "sdp",
      "set-payment-initiation": "setpay",
      "set-registration-initiation": "setreg",
      "shf+xml": "shf",
      "sparql-query": "rq",
      "sparql-results+xml": "srx",
      "srgs": "gram",
      "srgs+xml": "grxml",
      "sru+xml": "sru",
      "ssdl+xml": "ssdl",
      "ssml+xml": "ssml",
      "tei+xml": [
        "tei",
        "teicorpus"
      ],
      "thraud+xml": "tfi",
      "timestamped-data": "tsd",
      "vnd.3gpp.pic-bw-large": "plb",
      "vnd.3gpp.pic-bw-small": "psb",
      "vnd.3gpp.pic-bw-var": "pvb",
      "vnd.3gpp2.tcap": "tcap",
      "vnd.3m.post-it-notes": "pwn",
      "vnd.accpac.simply.aso": "aso",
      "vnd.accpac.simply.imp": "imp",
      "vnd.acucobol": "acu",
      "vnd.acucorp": [
        "atc",
        "acutc"
      ],
      "vnd.adobe.air-application-installer-package+zip": "air",
      "vnd.adobe.formscentral.fcdt": "fcdt",
      "vnd.adobe.fxp": [
        "fxp",
        "fxpl"
      ],
      "vnd.adobe.xdp+xml": "xdp",
      "vnd.adobe.xfdf": "xfdf",
      "vnd.ahead.space": "ahead",
      "vnd.airzip.filesecure.azf": "azf",
      "vnd.airzip.filesecure.azs": "azs",
      "vnd.amazon.ebook": "azw",
      "vnd.americandynamics.acc": "acc",
      "vnd.amiga.ami": "ami",
      "vnd.anser-web-certificate-issue-initiation": "cii",
      "vnd.anser-web-funds-transfer-initiation": "fti",
      "vnd.antix.game-component": "atx",
      "vnd.apple.installer+xml": "mpkg",
      "vnd.apple.mpegurl": "m3u8",
      "vnd.aristanetworks.swi": "swi",
      "vnd.astraea-software.iota": "iota",
      "vnd.audiograph": "aep",
      "vnd.blueice.multipass": "mpm",
      "vnd.bmi": "bmi",
      "vnd.businessobjects": "rep",
      "vnd.chemdraw+xml": "cdxml",
      "vnd.chipnuts.karaoke-mmd": "mmd",
      "vnd.claymore": "cla",
      "vnd.cloanto.rp9": "rp9",
      "vnd.clonk.c4group": [
        "c4g",
        "c4d",
        "c4f",
        "c4p",
        "c4u"
      ],
      "vnd.cluetrust.cartomobile-config": "c11amc",
      "vnd.cluetrust.cartomobile-config-pkg": "c11amz",
      "vnd.commonspace": "csp",
      "vnd.contact.cmsg": "cdbcmsg",
      "vnd.cosmocaller": "cmc",
      "vnd.crick.clicker": "clkx",
      "vnd.crick.clicker.keyboard": "clkk",
      "vnd.crick.clicker.palette": "clkp",
      "vnd.crick.clicker.template": "clkt",
      "vnd.crick.clicker.wordbank": "clkw",
      "vnd.criticaltools.wbs+xml": "wbs",
      "vnd.ctc-posml": "pml",
      "vnd.cups-ppd": "ppd",
      "vnd.curl.car": "car",
      "vnd.curl.pcurl": "pcurl",
      "vnd.dart": "dart",
      "vnd.data-vision.rdz": "rdz",
      "vnd.dece.data": [
        "uvf",
        "uvvf",
        "uvd",
        "uvvd"
      ],
      "vnd.dece.ttml+xml": [
        "uvt",
        "uvvt"
      ],
      "vnd.dece.unspecified": [
        "uvx",
        "uvvx"
      ],
      "vnd.dece.zip": [
        "uvz",
        "uvvz"
      ],
      "vnd.denovo.fcselayout-link": "fe_launch",
      "vnd.dna": "dna",
      "vnd.dolby.mlp": "mlp",
      "vnd.dpgraph": "dpg",
      "vnd.dreamfactory": "dfac",
      "vnd.ds-keypoint": "kpxx",
      "vnd.dvb.ait": "ait",
      "vnd.dvb.service": "svc",
      "vnd.dynageo": "geo",
      "vnd.ecowin.chart": "mag",
      "vnd.enliven": "nml",
      "vnd.epson.esf": "esf",
      "vnd.epson.msf": "msf",
      "vnd.epson.quickanime": "qam",
      "vnd.epson.salt": "slt",
      "vnd.epson.ssf": "ssf",
      "vnd.eszigno3+xml": [
        "es3",
        "et3"
      ],
      "vnd.ezpix-album": "ez2",
      "vnd.ezpix-package": "ez3",
      "vnd.fdf": "fdf",
      "vnd.fdsn.mseed": "mseed",
      "vnd.fdsn.seed": [
        "seed",
        "dataless"
      ],
      "vnd.flographit": "gph",
      "vnd.fluxtime.clip": "ftc",
      "vnd.framemaker": [
        "fm",
        "frame",
        "maker",
        "book"
      ],
      "vnd.frogans.fnc": "fnc",
      "vnd.frogans.ltf": "ltf",
      "vnd.fsc.weblaunch": "fsc",
      "vnd.fujitsu.oasys": "oas",
      "vnd.fujitsu.oasys2": "oa2",
      "vnd.fujitsu.oasys3": "oa3",
      "vnd.fujitsu.oasysgp": "fg5",
      "vnd.fujitsu.oasysprs": "bh2",
      "vnd.fujixerox.ddd": "ddd",
      "vnd.fujixerox.docuworks": "xdw",
      "vnd.fujixerox.docuworks.binder": "xbd",
      "vnd.fuzzysheet": "fzs",
      "vnd.genomatix.tuxedo": "txd",
      "vnd.geogebra.file": "ggb",
      "vnd.geogebra.tool": "ggt",
      "vnd.geometry-explorer": [
        "gex",
        "gre"
      ],
      "vnd.geonext": "gxt",
      "vnd.geoplan": "g2w",
      "vnd.geospace": "g3w",
      "vnd.gmx": "gmx",
      "vnd.grafeq": [
        "gqf",
        "gqs"
      ],
      "vnd.groove-account": "gac",
      "vnd.groove-help": "ghf",
      "vnd.groove-identity-message": "gim",
      "vnd.groove-injector": "grv",
      "vnd.groove-tool-message": "gtm",
      "vnd.groove-tool-template": "tpl",
      "vnd.groove-vcard": "vcg",
      "vnd.hal+xml": "hal",
      "vnd.handheld-entertainment+xml": "zmm",
      "vnd.hbci": "hbci",
      "vnd.hhe.lesson-player": "les",
      "vnd.hp-hpgl": "hpgl",
      "vnd.hp-hpid": "hpid",
      "vnd.hp-hps": "hps",
      "vnd.hp-jlyt": "jlt",
      "vnd.hp-pcl": "pcl",
      "vnd.hp-pclxl": "pclxl",
      "vnd.hydrostatix.sof-data": "sfd-hdstx",
      "vnd.ibm.minipay": "mpy",
      "vnd.ibm.modcap": [
        "afp",
        "listafp",
        "list3820"
      ],
      "vnd.ibm.rights-management": "irm",
      "vnd.ibm.secure-container": "sc",
      "vnd.iccprofile": [
        "icc",
        "icm"
      ],
      "vnd.igloader": "igl",
      "vnd.immervision-ivp": "ivp",
      "vnd.immervision-ivu": "ivu",
      "vnd.insors.igm": "igm",
      "vnd.intercon.formnet": [
        "xpw",
        "xpx"
      ],
      "vnd.intergeo": "i2g",
      "vnd.intu.qbo": "qbo",
      "vnd.intu.qfx": "qfx",
      "vnd.ipunplugged.rcprofile": "rcprofile",
      "vnd.irepository.package+xml": "irp",
      "vnd.is-xpr": "xpr",
      "vnd.isac.fcs": "fcs",
      "vnd.jam": "jam",
      "vnd.jcp.javame.midlet-rms": "rms",
      "vnd.jisp": "jisp",
      "vnd.joost.joda-archive": "joda",
      "vnd.kahootz": [
        "ktz",
        "ktr"
      ],
      "vnd.kde.karbon": "karbon",
      "vnd.kde.kchart": "chrt",
      "vnd.kde.kformula": "kfo",
      "vnd.kde.kivio": "flw",
      "vnd.kde.kontour": "kon",
      "vnd.kde.kpresenter": [
        "kpr",
        "kpt"
      ],
      "vnd.kde.kspread": "ksp",
      "vnd.kde.kword": [
        "kwd",
        "kwt"
      ],
      "vnd.kenameaapp": "htke",
      "vnd.kidspiration": "kia",
      "vnd.kinar": [
        "kne",
        "knp"
      ],
      "vnd.koan": [
        "skp",
        "skd",
        "skt",
        "skm"
      ],
      "vnd.kodak-descriptor": "sse",
      "vnd.las.las+xml": "lasxml",
      "vnd.llamagraphics.life-balance.desktop": "lbd",
      "vnd.llamagraphics.life-balance.exchange+xml": "lbe",
      "vnd.lotus-1-2-3": "123",
      "vnd.lotus-approach": "apr",
      "vnd.lotus-freelance": "pre",
      "vnd.lotus-notes": "nsf",
      "vnd.lotus-organizer": "org",
      "vnd.lotus-screencam": "scm",
      "vnd.lotus-wordpro": "lwp",
      "vnd.macports.portpkg": "portpkg",
      "vnd.mcd": "mcd",
      "vnd.medcalcdata": "mc1",
      "vnd.mediastation.cdkey": "cdkey",
      "vnd.mfer": "mwf",
      "vnd.mfmp": "mfm",
      "vnd.micrografx.flo": "flo",
      "vnd.micrografx.igx": "igx",
      "vnd.mif": "mif",
      "vnd.mobius.daf": "daf",
      "vnd.mobius.dis": "dis",
      "vnd.mobius.mbk": "mbk",
      "vnd.mobius.mqy": "mqy",
      "vnd.mobius.msl": "msl",
      "vnd.mobius.plc": "plc",
      "vnd.mobius.txf": "txf",
      "vnd.mophun.application": "mpn",
      "vnd.mophun.certificate": "mpc",
      "vnd.ms-artgalry": "cil",
      "vnd.ms-cab-compressed": "cab",
      "vnd.ms-excel.addin.macroenabled.12": "xlam",
      "vnd.ms-excel.sheet.binary.macroenabled.12": "xlsb",
      "vnd.ms-excel.sheet.macroenabled.12": "xlsm",
      "vnd.ms-excel.template.macroenabled.12": "xltm",
      "vnd.ms-fontobject": "eot",
      "vnd.ms-htmlhelp": "chm",
      "vnd.ms-ims": "ims",
      "vnd.ms-lrm": "lrm",
      "vnd.ms-officetheme": "thmx",
      "vnd.ms-powerpoint.addin.macroenabled.12": "ppam",
      "vnd.ms-powerpoint.presentation.macroenabled.12": "pptm",
      "vnd.ms-powerpoint.slide.macroenabled.12": "sldm",
      "vnd.ms-powerpoint.slideshow.macroenabled.12": "ppsm",
      "vnd.ms-powerpoint.template.macroenabled.12": "potm",
      "vnd.ms-project": [
        "mpp",
        "mpt"
      ],
      "vnd.ms-word.document.macroenabled.12": "docm",
      "vnd.ms-word.template.macroenabled.12": "dotm",
      "vnd.ms-works": [
        "wps",
        "wks",
        "wcm",
        "wdb"
      ],
      "vnd.ms-wpl": "wpl",
      "vnd.ms-xpsdocument": "xps",
      "vnd.mseq": "mseq",
      "vnd.musician": "mus",
      "vnd.muvee.style": "msty",
      "vnd.mynfc": "taglet",
      "vnd.neurolanguage.nlu": "nlu",
      "vnd.nitf": [
        "ntf",
        "nitf"
      ],
      "vnd.noblenet-directory": "nnd",
      "vnd.noblenet-sealer": "nns",
      "vnd.noblenet-web": "nnw",
      "vnd.nokia.n-gage.data": "ngdat",
      "vnd.nokia.n-gage.symbian.install": "n-gage",
      "vnd.nokia.radio-preset": "rpst",
      "vnd.nokia.radio-presets": "rpss",
      "vnd.novadigm.edm": "edm",
      "vnd.novadigm.edx": "edx",
      "vnd.novadigm.ext": "ext",
      "vnd.oasis.opendocument.chart-template": "otc",
      "vnd.oasis.opendocument.formula-template": "odft",
      "vnd.oasis.opendocument.image-template": "oti",
      "vnd.olpc-sugar": "xo",
      "vnd.oma.dd2+xml": "dd2",
      "vnd.openofficeorg.extension": "oxt",
      "vnd.openxmlformats-officedocument.presentationml.slide": "sldx",
      "vnd.osgeo.mapguide.package": "mgp",
      "vnd.osgi.dp": "dp",
      "vnd.osgi.subsystem": "esa",
      "vnd.palm": [
        "pdb",
        "pqa",
        "oprc"
      ],
      "vnd.pawaafile": "paw",
      "vnd.pg.format": "str",
      "vnd.pg.osasli": "ei6",
      "vnd.picsel": "efif",
      "vnd.pmi.widget": "wg",
      "vnd.pocketlearn": "plf",
      "vnd.powerbuilder6": "pbd",
      "vnd.previewsystems.box": "box",
      "vnd.proteus.magazine": "mgz",
      "vnd.publishare-delta-tree": "qps",
      "vnd.pvi.ptid1": "ptid",
      "vnd.quark.quarkxpress": [
        "qxd",
        "qxt",
        "qwd",
        "qwt",
        "qxl",
        "qxb"
      ],
      "vnd.realvnc.bed": "bed",
      "vnd.recordare.musicxml": "mxl",
      "vnd.recordare.musicxml+xml": "musicxml",
      "vnd.rig.cryptonote": "cryptonote",
      "vnd.rn-realmedia": "rm",
      "vnd.rn-realmedia-vbr": "rmvb",
      "vnd.route66.link66+xml": "link66",
      "vnd.sailingtracker.track": "st",
      "vnd.seemail": "see",
      "vnd.sema": "sema",
      "vnd.semd": "semd",
      "vnd.semf": "semf",
      "vnd.shana.informed.formdata": "ifm",
      "vnd.shana.informed.formtemplate": "itp",
      "vnd.shana.informed.interchange": "iif",
      "vnd.shana.informed.package": "ipk",
      "vnd.simtech-mindmapper": [
        "twd",
        "twds"
      ],
      "vnd.smart.teacher": "teacher",
      "vnd.solent.sdkm+xml": [
        "sdkm",
        "sdkd"
      ],
      "vnd.spotfire.dxp": "dxp",
      "vnd.spotfire.sfs": "sfs",
      "vnd.stepmania.package": "smzip",
      "vnd.stepmania.stepchart": "sm",
      "vnd.sus-calendar": [
        "sus",
        "susp"
      ],
      "vnd.svd": "svd",
      "vnd.syncml+xml": "xsm",
      "vnd.syncml.dm+wbxml": "bdm",
      "vnd.syncml.dm+xml": "xdm",
      "vnd.tao.intent-module-archive": "tao",
      "vnd.tcpdump.pcap": [
        "pcap",
        "cap",
        "dmp"
      ],
      "vnd.tmobile-livetv": "tmo",
      "vnd.trid.tpt": "tpt",
      "vnd.triscape.mxs": "mxs",
      "vnd.trueapp": "tra",
      "vnd.ufdl": [
        "ufd",
        "ufdl"
      ],
      "vnd.uiq.theme": "utz",
      "vnd.umajin": "umj",
      "vnd.unity": "unityweb",
      "vnd.uoml+xml": "uoml",
      "vnd.vcx": "vcx",
      "vnd.visionary": "vis",
      "vnd.vsf": "vsf",
      "vnd.webturbo": "wtb",
      "vnd.wolfram.player": "nbp",
      "vnd.wqd": "wqd",
      "vnd.wt.stf": "stf",
      "vnd.xara": "xar",
      "vnd.xfdl": "xfdl",
      "vnd.yamaha.hv-dic": "hvd",
      "vnd.yamaha.hv-script": "hvs",
      "vnd.yamaha.hv-voice": "hvp",
      "vnd.yamaha.openscoreformat": "osf",
      "vnd.yamaha.openscoreformat.osfpvg+xml": "osfpvg",
      "vnd.yamaha.smaf-audio": "saf",
      "vnd.yamaha.smaf-phrase": "spf",
      "vnd.yellowriver-custom-menu": "cmp",
      "vnd.zul": [
        "zir",
        "zirz"
      ],
      "vnd.zzazz.deck+xml": "zaz",
      "voicexml+xml": "vxml",
      "widget": "wgt",
      "winhlp": "hlp",
      "wsdl+xml": "wsdl",
      "wspolicy+xml": "wspolicy",
      "x-ace-compressed": "ace",
      "x-authorware-bin": [
        "aab",
        "x32",
        "u32",
        "vox"
      ],
      "x-authorware-map": "aam",
      "x-authorware-seg": "aas",
      "x-blorb": [
        "blb",
        "blorb"
      ],
      "x-bzip": "bz",
      "x-bzip2": [
        "bz2",
        "boz"
      ],
      "x-cfs-compressed": "cfs",
      "x-chat": "chat",
      "x-conference": "nsc",
      "x-dgc-compressed": "dgc",
      "x-dtbncx+xml": "ncx",
      "x-dtbook+xml": "dtb",
      "x-dtbresource+xml": "res",
      "x-eva": "eva",
      "x-font-bdf": "bdf",
      "x-font-ghostscript": "gsf",
      "x-font-linux-psf": "psf",
      "x-font-pcf": "pcf",
      "x-font-snf": "snf",
      "x-font-ttf": [
        "ttf",
        "ttc"
      ],
      "x-font-type1": [
        "pfa",
        "pfb",
        "pfm",
        "afm"
      ],
      "x-freearc": "arc",
      "x-gca-compressed": "gca",
      "x-glulx": "ulx",
      "x-gramps-xml": "gramps",
      "x-install-instructions": "install",
      "x-lzh-compressed": [
        "lzh",
        "lha"
      ],
      "x-mie": "mie",
      "x-mobipocket-ebook": [
        "prc",
        "mobi"
      ],
      "x-ms-application": "application",
      "x-ms-shortcut": "lnk",
      "x-ms-xbap": "xbap",
      "x-msbinder": "obd",
      "x-mscardfile": "crd",
      "x-msclip": "clp",
      "application/x-ms-installer": "msi",
      "x-msmediaview": [
        "mvb",
        "m13",
        "m14"
      ],
      "x-msmetafile": [
        "wmf",
        "wmz",
        "emf",
        "emz"
      ],
      "x-msmoney": "mny",
      "x-mspublisher": "pub",
      "x-msschedule": "scd",
      "x-msterminal": "trm",
      "x-mswrite": "wri",
      "x-nzb": "nzb",
      "x-pkcs12": [
        "p12",
        "pfx"
      ],
      "x-pkcs7-certificates": [
        "p7b",
        "spc"
      ],
      "x-research-info-systems": "ris",
      "x-silverlight-app": "xap",
      "x-sql": "sql",
      "x-stuffitx": "sitx",
      "x-subrip": "srt",
      "x-t3vm-image": "t3",
      "x-tex-tfm": "tfm",
      "x-tgif": "obj",
      "x-xliff+xml": "xlf",
      "x-xz": "xz",
      "x-zmachine": [
        "z1",
        "z2",
        "z3",
        "z4",
        "z5",
        "z6",
        "z7",
        "z8"
      ],
      "xaml+xml": "xaml",
      "xcap-diff+xml": "xdf",
      "xenc+xml": "xenc",
      "xml-dtd": "dtd",
      "xop+xml": "xop",
      "xproc+xml": "xpl",
      "xslt+xml": "xslt",
      "xv+xml": [
        "mxml",
        "xhvml",
        "xvml",
        "xvm"
      ],
      "yang": "yang",
      "yin+xml": "yin",
      "envoy": "evy",
      "fractals": "fif",
      "internet-property-stream": "acx",
      "olescript": "axs",
      "vnd.ms-outlook": "msg",
      "vnd.ms-pkicertstore": "sst",
      "x-compress": "z",
      "x-perfmon": [
        "pma",
        "pmc",
        "pmr",
        "pmw"
      ],
      "ynd.ms-pkipko": "pko",
      "gzip": [
        "gz",
        "tgz"
      ],
      "smil+xml": [
        "smi",
        "smil"
      ],
      "vnd.debian.binary-package": [
        "deb",
        "udeb"
      ],
      "vnd.hzn-3d-crossword": "x3d",
      "vnd.sqlite3": [
        "db",
        "sqlite",
        "sqlite3",
        "db-wal",
        "sqlite-wal",
        "db-shm",
        "sqlite-shm"
      ],
      "vnd.wap.sic": "sic",
      "vnd.wap.slc": "slc",
      "x-krita": [
        "kra",
        "krz"
      ],
      "x-perl": [
        "pm",
        "pl"
      ],
      "yaml": [
        "yaml",
        "yml"
      ]
    },
    "audio": {
      "amr": "amr",
      "amr-wb": "awb",
      "annodex": "axa",
      "basic": [
        "au",
        "snd"
      ],
      "flac": "flac",
      "midi": [
        "mid",
        "midi",
        "kar",
        "rmi"
      ],
      "mpeg": [
        "mpga",
        "mpega",
        "mp3",
        "m4a",
        "mp2a",
        "m2a",
        "m3a"
      ],
      "mpegurl": "m3u",
      "ogg": [
        "oga",
        "ogg",
        "spx"
      ],
      "prs.sid": "sid",
      "x-aiff": "aifc",
      "x-gsm": "gsm",
      "x-ms-wma": "wma",
      "x-ms-wax": "wax",
      "x-pn-realaudio": "ram",
      "x-realaudio": "ra",
      "x-sd2": "sd2",
      "adpcm": "adp",
      "mp4": "mp4a",
      "s3m": "s3m",
      "silk": "sil",
      "vnd.dece.audio": [
        "uva",
        "uvva"
      ],
      "vnd.digital-winds": "eol",
      "vnd.dra": "dra",
      "vnd.dts": "dts",
      "vnd.dts.hd": "dtshd",
      "vnd.lucent.voice": "lvp",
      "vnd.ms-playready.media.pya": "pya",
      "vnd.nuera.ecelp4800": "ecelp4800",
      "vnd.nuera.ecelp7470": "ecelp7470",
      "vnd.nuera.ecelp9600": "ecelp9600",
      "vnd.rip": "rip",
      "webm": "weba",
      "x-caf": "caf",
      "x-matroska": "mka",
      "x-pn-realaudio-plugin": "rmp",
      "xm": "xm",
      "aac": "aac",
      "aiff": [
        "aiff",
        "aif",
        "aff"
      ],
      "opus": "opus",
      "wav": "wav"
    },
    "chemical": {
      "x-alchemy": "alc",
      "x-cache": [
        "cac",
        "cache"
      ],
      "x-cache-csf": "csf",
      "x-cactvs-binary": [
        "cbin",
        "cascii",
        "ctab"
      ],
      "x-cdx": "cdx",
      "x-chem3d": "c3d",
      "x-cif": "cif",
      "x-cmdf": "cmdf",
      "x-cml": "cml",
      "x-compass": "cpa",
      "x-crossfire": "bsd",
      "x-csml": [
        "csml",
        "csm"
      ],
      "x-ctx": "ctx",
      "x-cxf": [
        "cxf",
        "cef"
      ],
      "x-embl-dl-nucleotide": [
        "emb",
        "embl"
      ],
      "x-gamess-input": [
        "inp",
        "gam",
        "gamin"
      ],
      "x-gaussian-checkpoint": [
        "fch",
        "fchk"
      ],
      "x-gaussian-cube": "cub",
      "x-gaussian-input": [
        "gau",
        "gjc",
        "gjf"
      ],
      "x-gaussian-log": "gal",
      "x-gcg8-sequence": "gcg",
      "x-genbank": "gen",
      "x-hin": "hin",
      "x-isostar": [
        "istr",
        "ist"
      ],
      "x-jcamp-dx": [
        "jdx",
        "dx"
      ],
      "x-kinemage": "kin",
      "x-macmolecule": "mcm",
      "x-macromodel-input": "mmod",
      "x-mdl-molfile": "mol",
      "x-mdl-rdfile": "rd",
      "x-mdl-rxnfile": "rxn",
      "x-mdl-sdfile": "sd",
      "x-mdl-tgf": "tgf",
      "x-mmcif": "mcif",
      "x-mol2": "mol2",
      "x-molconn-Z": "b",
      "x-mopac-graph": "gpt",
      "x-mopac-input": [
        "mop",
        "mopcrt",
        "zmt"
      ],
      "x-mopac-out": "moo",
      "x-ncbi-asn1": "asn",
      "x-ncbi-asn1-ascii": [
        "prt",
        "ent"
      ],
      "x-ncbi-asn1-binary": "val",
      "x-rosdal": "ros",
      "x-swissprot": "sw",
      "x-vamas-iso14976": "vms",
      "x-vmd": "vmd",
      "x-xtel": "xtel",
      "x-xyz": "xyz"
    },
    "font": {
      "otf": "otf",
      "woff": "woff",
      "woff2": "woff2"
    },
    "image": {
      "gif": "gif",
      "ief": "ief",
      "jpeg": [
        "jpeg",
        "jpg",
        "jpe",
        "jfif",
        "jfif-tbnl",
        "jif"
      ],
      "pcx": "pcx",
      "png": "png",
      "svg+xml": [
        "svg",
        "svgz"
      ],
      "tiff": [
        "tiff",
        "tif"
      ],
      "vnd.djvu": [
        "djvu",
        "djv"
      ],
      "vnd.wap.wbmp": "wbmp",
      "x-canon-cr2": "cr2",
      "x-canon-crw": "crw",
      "x-cmu-raster": "ras",
      "x-coreldraw": "cdr",
      "x-coreldrawpattern": "pat",
      "x-coreldrawtemplate": "cdt",
      "x-corelphotopaint": "cpt",
      "x-epson-erf": "erf",
      "x-icon": "ico",
      "x-jg": "art",
      "x-jng": "jng",
      "x-nikon-nef": "nef",
      "x-olympus-orf": "orf",
      "x-portable-anymap": "pnm",
      "x-portable-bitmap": "pbm",
      "x-portable-graymap": "pgm",
      "x-portable-pixmap": "ppm",
      "x-rgb": "rgb",
      "x-xbitmap": "xbm",
      "x-xpixmap": "xpm",
      "x-xwindowdump": "xwd",
      "bmp": "bmp",
      "cgm": "cgm",
      "g3fax": "g3",
      "ktx": "ktx",
      "prs.btif": "btif",
      "sgi": "sgi",
      "vnd.dece.graphic": [
        "uvi",
        "uvvi",
        "uvg",
        "uvvg"
      ],
      "vnd.dwg": "dwg",
      "vnd.dxf": "dxf",
      "vnd.fastbidsheet": "fbs",
      "vnd.fpx": "fpx",
      "vnd.fst": "fst",
      "vnd.fujixerox.edmics-mmr": "mmr",
      "vnd.fujixerox.edmics-rlc": "rlc",
      "vnd.ms-modi": "mdi",
      "vnd.ms-photo": "wdp",
      "vnd.net-fpx": "npx",
      "vnd.xiff": "xif",
      "webp": "webp",
      "x-3ds": "3ds",
      "x-cmx": "cmx",
      "x-freehand": [
        "fh",
        "fhc",
        "fh4",
        "fh5",
        "fh7"
      ],
      "x-pict": [
        "pic",
        "pct"
      ],
      "x-tga": "tga",
      "cis-cod": "cod",
      "avif": "avifs",
      "heic": [
        "heif",
        "heic"
      ],
      "pjpeg": [
        "pjpg"
      ],
      "vnd.adobe.photoshop": "psd",
      "x-adobe-dng": "dng",
      "x-fuji-raf": "raf",
      "x-icns": "icns",
      "x-kodak-dcr": "dcr",
      "x-kodak-k25": "k25",
      "x-kodak-kdc": "kdc",
      "x-minolta-mrw": "mrw",
      "x-panasonic-raw": [
        "raw",
        "rw2",
        "rwl"
      ],
      "x-pentax-pef": [
        "pef",
        "ptx"
      ],
      "x-sigma-x3f": "x3f",
      "x-sony-arw": "arw",
      "x-sony-sr2": "sr2",
      "x-sony-srf": "srf"
    },
    "message": {
      "rfc822": [
        "eml",
        "mime",
        "mht",
        "mhtml",
        "nws"
      ]
    },
    "model": {
      "iges": [
        "igs",
        "iges"
      ],
      "mesh": [
        "msh",
        "mesh",
        "silo"
      ],
      "vrml": [
        "wrl",
        "vrml"
      ],
      "x3d+vrml": [
        "x3dv",
        "x3dvz"
      ],
      "x3d+xml": "x3dz",
      "x3d+binary": [
        "x3db",
        "x3dbz"
      ],
      "vnd.collada+xml": "dae",
      "vnd.dwf": "dwf",
      "vnd.gdl": "gdl",
      "vnd.gtw": "gtw",
      "vnd.mts": "mts",
      "vnd.usdz+zip": "usdz",
      "vnd.vtu": "vtu"
    },
    "text": {
      "cache-manifest": [
        "manifest",
        "appcache"
      ],
      "calendar": [
        "ics",
        "icz",
        "ifb"
      ],
      "css": "css",
      "csv": "csv",
      "h323": "323",
      "html": [
        "html",
        "htm",
        "shtml",
        "stm"
      ],
      "iuls": "uls",
      "plain": [
        "txt",
        "text",
        "brf",
        "conf",
        "def",
        "list",
        "log",
        "in",
        "bas",
        "diff",
        "ksh"
      ],
      "richtext": "rtx",
      "scriptlet": [
        "sct",
        "wsc"
      ],
      "texmacs": "tm",
      "tab-separated-values": "tsv",
      "vnd.sun.j2me.app-descriptor": "jad",
      "vnd.wap.wml": "wml",
      "vnd.wap.wmlscript": "wmls",
      "x-bibtex": "bib",
      "x-boo": "boo",
      "x-c++hdr": [
        "h++",
        "hpp",
        "hxx",
        "hh"
      ],
      "x-c++src": [
        "c++",
        "cpp",
        "cxx",
        "cc"
      ],
      "x-component": "htc",
      "x-dsrc": "d",
      "x-diff": "patch",
      "x-haskell": "hs",
      "x-java": "java",
      "x-literate-haskell": "lhs",
      "x-moc": "moc",
      "x-pascal": [
        "p",
        "pas",
        "pp",
        "inc"
      ],
      "x-pcs-gcd": "gcd",
      "x-python": "py",
      "x-scala": "scala",
      "x-setext": "etx",
      "x-tcl": [
        "tcl",
        "tk"
      ],
      "x-tex": [
        "tex",
        "ltx",
        "sty",
        "cls"
      ],
      "x-vcalendar": "vcs",
      "x-vcard": "vcf",
      "n3": "n3",
      "prs.lines.tag": "dsc",
      "sgml": [
        "sgml",
        "sgm"
      ],
      "troff": [
        "t",
        "tr",
        "roff",
        "man",
        "me",
        "ms"
      ],
      "turtle": "ttl",
      "uri-list": [
        "uri",
        "uris",
        "urls"
      ],
      "vcard": "vcard",
      "vnd.curl": "curl",
      "vnd.curl.dcurl": "dcurl",
      "vnd.curl.scurl": "scurl",
      "vnd.curl.mcurl": "mcurl",
      "vnd.dvb.subtitle": "sub",
      "vnd.fly": "fly",
      "vnd.fmi.flexstor": "flx",
      "vnd.graphviz": "gv",
      "vnd.in3d.3dml": "3dml",
      "vnd.in3d.spot": "spot",
      "x-asm": [
        "s",
        "asm"
      ],
      "x-c": [
        "c",
        "h",
        "dic"
      ],
      "x-fortran": [
        "f",
        "for",
        "f77",
        "f90"
      ],
      "x-opml": "opml",
      "x-nfo": "nfo",
      "x-sfv": "sfv",
      "x-uuencode": "uu",
      "webviewhtml": "htt",
      "javascript": "js",
      "json": "json",
      "markdown": [
        "md",
        "markdown",
        "mdown",
        "markdn"
      ],
      "vnd.wap.si": "si",
      "vnd.wap.sl": "sl"
    },
    "video": {
      "avif": "avif",
      "3gpp": "3gp",
      "annodex": "axv",
      "dl": "dl",
      "dv": [
        "dif",
        "dv"
      ],
      "fli": "fli",
      "gl": "gl",
      "mpeg": [
        "mpeg",
        "mpg",
        "mpe",
        "m1v",
        "m2v",
        "mp2",
        "mpa",
        "mpv2"
      ],
      "mp4": [
        "mp4",
        "mp4v",
        "mpg4"
      ],
      "quicktime": [
        "qt",
        "mov"
      ],
      "ogg": "ogv",
      "vnd.mpegurl": [
        "mxu",
        "m4u"
      ],
      "x-flv": "flv",
      "x-la-asf": [
        "lsf",
        "lsx"
      ],
      "x-mng": "mng",
      "x-ms-asf": [
        "asf",
        "asx",
        "asr"
      ],
      "x-ms-wm": "wm",
      "x-ms-wmv": "wmv",
      "x-ms-wmx": "wmx",
      "x-ms-wvx": "wvx",
      "x-msvideo": "avi",
      "x-sgi-movie": "movie",
      "x-matroska": [
        "mpv",
        "mkv",
        "mk3d",
        "mks"
      ],
      "3gpp2": "3g2",
      "h261": "h261",
      "h263": "h263",
      "h264": "h264",
      "jpeg": "jpgv",
      "jpm": [
        "jpm",
        "jpgm"
      ],
      "mj2": [
        "mj2",
        "mjp2"
      ],
      "vnd.dece.hd": [
        "uvh",
        "uvvh"
      ],
      "vnd.dece.mobile": [
        "uvm",
        "uvvm"
      ],
      "vnd.dece.pd": [
        "uvp",
        "uvvp"
      ],
      "vnd.dece.sd": [
        "uvs",
        "uvvs"
      ],
      "vnd.dece.video": [
        "uvv",
        "uvvv"
      ],
      "vnd.dvb.file": "dvb",
      "vnd.fvt": "fvt",
      "vnd.ms-playready.media.pyv": "pyv",
      "vnd.uvvu.mp4": [
        "uvu",
        "uvvu"
      ],
      "vnd.vivo": "viv",
      "webm": "webm",
      "x-f4v": "f4v",
      "x-m4v": "m4v",
      "x-ms-vob": "vob",
      "x-smv": "smv",
      "mp2t": "ts"
    },
    "x-conference": {
      "x-cooltalk": "ice"
    },
    "x-world": {
      "x-vrml": [
        "vrm",
        "flr",
        "wrz",
        "xaf",
        "xof"
      ]
    }
  };
  var mimeTypes = (() => {
    const mimeTypes2 = {};
    for (const type of Object.keys(table)) {
      for (const subtype of Object.keys(table[type])) {
        const value = table[type][subtype];
        if (typeof value == "string") {
          mimeTypes2[value] = type + "/" + subtype;
        } else {
          for (let indexMimeType = 0; indexMimeType < value.length; indexMimeType++) {
            mimeTypes2[value[indexMimeType]] = type + "/" + subtype;
          }
        }
      }
    }
    return mimeTypes2;
  })();

  // lib/zipjs/lib/core/streams/codecs/crc32.js
  var table2 = [];
  for (let i = 0; i < 256; i++) {
    let t = i;
    for (let j = 0; j < 8; j++) {
      if (t & 1) {
        t = t >>> 1 ^ 3988292384;
      } else {
        t = t >>> 1;
      }
    }
    table2[i] = t;
  }
  var Crc32 = class {
    constructor(crc) {
      this.crc = crc || -1;
    }
    append(data) {
      let crc = this.crc | 0;
      for (let offset = 0, length = data.length | 0; offset < length; offset++) {
        crc = crc >>> 8 ^ table2[(crc ^ data[offset]) & 255];
      }
      this.crc = crc;
    }
    get() {
      return ~this.crc;
    }
  };

  // lib/zipjs/lib/core/streams/crc32-stream.js
  var Crc32Stream = class extends TransformStream {
    constructor() {
      let stream;
      const crc322 = new Crc32();
      super({
        transform(chunk, controller) {
          crc322.append(chunk);
          controller.enqueue(chunk);
        },
        flush() {
          const value = new Uint8Array(4);
          const dataView = new DataView(value.buffer);
          dataView.setUint32(0, crc322.get());
          stream.value = value;
        }
      });
      stream = this;
    }
  };

  // lib/zipjs/lib/core/util/encode-text.js
  function encodeText(value) {
    if (typeof TextEncoder == UNDEFINED_TYPE) {
      value = unescape(encodeURIComponent(value));
      const result = new Uint8Array(value.length);
      for (let i = 0; i < result.length; i++) {
        result[i] = value.charCodeAt(i);
      }
      return result;
    } else {
      return new TextEncoder().encode(value);
    }
  }

  // lib/zipjs/lib/core/streams/codecs/sjcl.js
  var bitArray = {
    /**
     * Concatenate two bit arrays.
     * @param {bitArray} a1 The first array.
     * @param {bitArray} a2 The second array.
     * @return {bitArray} The concatenation of a1 and a2.
     */
    concat(a1, a2) {
      if (a1.length === 0 || a2.length === 0) {
        return a1.concat(a2);
      }
      const last = a1[a1.length - 1], shift = bitArray.getPartial(last);
      if (shift === 32) {
        return a1.concat(a2);
      } else {
        return bitArray._shiftRight(a2, shift, last | 0, a1.slice(0, a1.length - 1));
      }
    },
    /**
     * Find the length of an array of bits.
     * @param {bitArray} a The array.
     * @return {Number} The length of a, in bits.
     */
    bitLength(a) {
      const l = a.length;
      if (l === 0) {
        return 0;
      }
      const x = a[l - 1];
      return (l - 1) * 32 + bitArray.getPartial(x);
    },
    /**
     * Truncate an array.
     * @param {bitArray} a The array.
     * @param {Number} len The length to truncate to, in bits.
     * @return {bitArray} A new array, truncated to len bits.
     */
    clamp(a, len) {
      if (a.length * 32 < len) {
        return a;
      }
      a = a.slice(0, Math.ceil(len / 32));
      const l = a.length;
      len = len & 31;
      if (l > 0 && len) {
        a[l - 1] = bitArray.partial(len, a[l - 1] & 2147483648 >> len - 1, 1);
      }
      return a;
    },
    /**
     * Make a partial word for a bit array.
     * @param {Number} len The number of bits in the word.
     * @param {Number} x The bits.
     * @param {Number} [_end=0] Pass 1 if x has already been shifted to the high side.
     * @return {Number} The partial word.
     */
    partial(len, x, _end) {
      if (len === 32) {
        return x;
      }
      return (_end ? x | 0 : x << 32 - len) + len * 1099511627776;
    },
    /**
     * Get the number of bits used by a partial word.
     * @param {Number} x The partial word.
     * @return {Number} The number of bits used by the partial word.
     */
    getPartial(x) {
      return Math.round(x / 1099511627776) || 32;
    },
    /** Shift an array right.
     * @param {bitArray} a The array to shift.
     * @param {Number} shift The number of bits to shift.
     * @param {Number} [carry=0] A byte to carry in
     * @param {bitArray} [out=[]] An array to prepend to the output.
     * @private
     */
    _shiftRight(a, shift, carry, out) {
      if (out === void 0) {
        out = [];
      }
      for (; shift >= 32; shift -= 32) {
        out.push(carry);
        carry = 0;
      }
      if (shift === 0) {
        return out.concat(a);
      }
      for (let i = 0; i < a.length; i++) {
        out.push(carry | a[i] >>> shift);
        carry = a[i] << 32 - shift;
      }
      const last2 = a.length ? a[a.length - 1] : 0;
      const shift2 = bitArray.getPartial(last2);
      out.push(bitArray.partial(shift + shift2 & 31, shift + shift2 > 32 ? carry : out.pop(), 1));
      return out;
    }
  };
  var codec = {
    bytes: {
      /** Convert from a bitArray to an array of bytes. */
      fromBits(arr) {
        const bl = bitArray.bitLength(arr);
        const byteLength = bl / 8;
        const out = new Uint8Array(byteLength);
        let tmp;
        for (let i = 0; i < byteLength; i++) {
          if ((i & 3) === 0) {
            tmp = arr[i / 4];
          }
          out[i] = tmp >>> 24;
          tmp <<= 8;
        }
        return out;
      },
      /** Convert from an array of bytes to a bitArray. */
      toBits(bytes) {
        const out = [];
        let i;
        let tmp = 0;
        for (i = 0; i < bytes.length; i++) {
          tmp = tmp << 8 | bytes[i];
          if ((i & 3) === 3) {
            out.push(tmp);
            tmp = 0;
          }
        }
        if (i & 3) {
          out.push(bitArray.partial(8 * (i & 3), tmp));
        }
        return out;
      }
    }
  };
  var hash = {};
  hash.sha1 = class {
    constructor(hash2) {
      const sha1 = this;
      sha1.blockSize = 512;
      sha1._init = [1732584193, 4023233417, 2562383102, 271733878, 3285377520];
      sha1._key = [1518500249, 1859775393, 2400959708, 3395469782];
      if (hash2) {
        sha1._h = hash2._h.slice(0);
        sha1._buffer = hash2._buffer.slice(0);
        sha1._length = hash2._length;
      } else {
        sha1.reset();
      }
    }
    /**
     * Reset the hash state.
     * @return this
     */
    reset() {
      const sha1 = this;
      sha1._h = sha1._init.slice(0);
      sha1._buffer = [];
      sha1._length = 0;
      return sha1;
    }
    /**
     * Input several words to the hash.
     * @param {bitArray|String} data the data to hash.
     * @return this
     */
    update(data) {
      const sha1 = this;
      if (typeof data === "string") {
        data = codec.utf8String.toBits(data);
      }
      const b = sha1._buffer = bitArray.concat(sha1._buffer, data);
      const ol = sha1._length;
      const nl = sha1._length = ol + bitArray.bitLength(data);
      if (nl > 9007199254740991) {
        throw new Error("Cannot hash more than 2^53 - 1 bits");
      }
      const c = new Uint32Array(b);
      let j = 0;
      for (let i = sha1.blockSize + ol - (sha1.blockSize + ol & sha1.blockSize - 1); i <= nl; i += sha1.blockSize) {
        sha1._block(c.subarray(16 * j, 16 * (j + 1)));
        j += 1;
      }
      b.splice(0, 16 * j);
      return sha1;
    }
    /**
     * Complete hashing and output the hash value.
     * @return {bitArray} The hash value, an array of 5 big-endian words. TODO
     */
    finalize() {
      const sha1 = this;
      let b = sha1._buffer;
      const h = sha1._h;
      b = bitArray.concat(b, [bitArray.partial(1, 1)]);
      for (let i = b.length + 2; i & 15; i++) {
        b.push(0);
      }
      b.push(Math.floor(sha1._length / 4294967296));
      b.push(sha1._length | 0);
      while (b.length) {
        sha1._block(b.splice(0, 16));
      }
      sha1.reset();
      return h;
    }
    /**
     * The SHA-1 logical functions f(0), f(1), ..., f(79).
     * @private
     */
    _f(t, b, c, d) {
      if (t <= 19) {
        return b & c | ~b & d;
      } else if (t <= 39) {
        return b ^ c ^ d;
      } else if (t <= 59) {
        return b & c | b & d | c & d;
      } else if (t <= 79) {
        return b ^ c ^ d;
      }
    }
    /**
     * Circular left-shift operator.
     * @private
     */
    _S(n, x) {
      return x << n | x >>> 32 - n;
    }
    /**
     * Perform one cycle of SHA-1.
     * @param {Uint32Array|bitArray} words one block of words.
     * @private
     */
    _block(words) {
      const sha1 = this;
      const h = sha1._h;
      const w = Array(80);
      for (let j = 0; j < 16; j++) {
        w[j] = words[j];
      }
      let a = h[0];
      let b = h[1];
      let c = h[2];
      let d = h[3];
      let e2 = h[4];
      for (let t = 0; t <= 79; t++) {
        if (t >= 16) {
          w[t] = sha1._S(1, w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16]);
        }
        const tmp = sha1._S(5, a) + sha1._f(t, b, c, d) + e2 + w[t] + sha1._key[Math.floor(t / 20)] | 0;
        e2 = d;
        d = c;
        c = sha1._S(30, b);
        b = a;
        a = tmp;
      }
      h[0] = h[0] + a | 0;
      h[1] = h[1] + b | 0;
      h[2] = h[2] + c | 0;
      h[3] = h[3] + d | 0;
      h[4] = h[4] + e2 | 0;
    }
  };
  var cipher = {};
  cipher.aes = class {
    constructor(key) {
      const aes = this;
      aes._tables = [[[], [], [], [], []], [[], [], [], [], []]];
      if (!aes._tables[0][0][0]) {
        aes._precompute();
      }
      const sbox = aes._tables[0][4];
      const decTable = aes._tables[1];
      const keyLen = key.length;
      let i, encKey, decKey, rcon = 1;
      if (keyLen !== 4 && keyLen !== 6 && keyLen !== 8) {
        throw new Error("invalid aes key size");
      }
      aes._key = [encKey = key.slice(0), decKey = []];
      for (i = keyLen; i < 4 * keyLen + 28; i++) {
        let tmp = encKey[i - 1];
        if (i % keyLen === 0 || keyLen === 8 && i % keyLen === 4) {
          tmp = sbox[tmp >>> 24] << 24 ^ sbox[tmp >> 16 & 255] << 16 ^ sbox[tmp >> 8 & 255] << 8 ^ sbox[tmp & 255];
          if (i % keyLen === 0) {
            tmp = tmp << 8 ^ tmp >>> 24 ^ rcon << 24;
            rcon = rcon << 1 ^ (rcon >> 7) * 283;
          }
        }
        encKey[i] = encKey[i - keyLen] ^ tmp;
      }
      for (let j = 0; i; j++, i--) {
        const tmp = encKey[j & 3 ? i : i - 4];
        if (i <= 4 || j < 4) {
          decKey[j] = tmp;
        } else {
          decKey[j] = decTable[0][sbox[tmp >>> 24]] ^ decTable[1][sbox[tmp >> 16 & 255]] ^ decTable[2][sbox[tmp >> 8 & 255]] ^ decTable[3][sbox[tmp & 255]];
        }
      }
    }
    // public
    /* Something like this might appear here eventually
    name: "AES",
    blockSize: 4,
    keySizes: [4,6,8],
    */
    /**
     * Encrypt an array of 4 big-endian words.
     * @param {Array} data The plaintext.
     * @return {Array} The ciphertext.
     */
    encrypt(data) {
      return this._crypt(data, 0);
    }
    /**
     * Decrypt an array of 4 big-endian words.
     * @param {Array} data The ciphertext.
     * @return {Array} The plaintext.
     */
    decrypt(data) {
      return this._crypt(data, 1);
    }
    /**
     * Expand the S-box tables.
     *
     * @private
     */
    _precompute() {
      const encTable = this._tables[0];
      const decTable = this._tables[1];
      const sbox = encTable[4];
      const sboxInv = decTable[4];
      const d = [];
      const th = [];
      let xInv, x2, x4, x8;
      for (let i = 0; i < 256; i++) {
        th[(d[i] = i << 1 ^ (i >> 7) * 283) ^ i] = i;
      }
      for (let x = xInv = 0; !sbox[x]; x ^= x2 || 1, xInv = th[xInv] || 1) {
        let s = xInv ^ xInv << 1 ^ xInv << 2 ^ xInv << 3 ^ xInv << 4;
        s = s >> 8 ^ s & 255 ^ 99;
        sbox[x] = s;
        sboxInv[s] = x;
        x8 = d[x4 = d[x2 = d[x]]];
        let tDec = x8 * 16843009 ^ x4 * 65537 ^ x2 * 257 ^ x * 16843008;
        let tEnc = d[s] * 257 ^ s * 16843008;
        for (let i = 0; i < 4; i++) {
          encTable[i][x] = tEnc = tEnc << 24 ^ tEnc >>> 8;
          decTable[i][s] = tDec = tDec << 24 ^ tDec >>> 8;
        }
      }
      for (let i = 0; i < 5; i++) {
        encTable[i] = encTable[i].slice(0);
        decTable[i] = decTable[i].slice(0);
      }
    }
    /**
     * Encryption and decryption core.
     * @param {Array} input Four words to be encrypted or decrypted.
     * @param dir The direction, 0 for encrypt and 1 for decrypt.
     * @return {Array} The four encrypted or decrypted words.
     * @private
     */
    _crypt(input, dir) {
      if (input.length !== 4) {
        throw new Error("invalid aes block size");
      }
      const key = this._key[dir];
      const nInnerRounds = key.length / 4 - 2;
      const out = [0, 0, 0, 0];
      const table3 = this._tables[dir];
      const t0 = table3[0];
      const t1 = table3[1];
      const t2 = table3[2];
      const t3 = table3[3];
      const sbox = table3[4];
      let a = input[0] ^ key[0];
      let b = input[dir ? 3 : 1] ^ key[1];
      let c = input[2] ^ key[2];
      let d = input[dir ? 1 : 3] ^ key[3];
      let kIndex = 4;
      let a2, b2, c2;
      for (let i = 0; i < nInnerRounds; i++) {
        a2 = t0[a >>> 24] ^ t1[b >> 16 & 255] ^ t2[c >> 8 & 255] ^ t3[d & 255] ^ key[kIndex];
        b2 = t0[b >>> 24] ^ t1[c >> 16 & 255] ^ t2[d >> 8 & 255] ^ t3[a & 255] ^ key[kIndex + 1];
        c2 = t0[c >>> 24] ^ t1[d >> 16 & 255] ^ t2[a >> 8 & 255] ^ t3[b & 255] ^ key[kIndex + 2];
        d = t0[d >>> 24] ^ t1[a >> 16 & 255] ^ t2[b >> 8 & 255] ^ t3[c & 255] ^ key[kIndex + 3];
        kIndex += 4;
        a = a2;
        b = b2;
        c = c2;
      }
      for (let i = 0; i < 4; i++) {
        out[dir ? 3 & -i : i] = sbox[a >>> 24] << 24 ^ sbox[b >> 16 & 255] << 16 ^ sbox[c >> 8 & 255] << 8 ^ sbox[d & 255] ^ key[kIndex++];
        a2 = a;
        a = b;
        b = c;
        c = d;
        d = a2;
      }
      return out;
    }
  };
  var random = {
    /** 
     * Generate random words with pure js, cryptographically not as strong & safe as native implementation.
     * @param {TypedArray} typedArray The array to fill.
     * @return {TypedArray} The random values.
     */
    getRandomValues(typedArray) {
      const words = new Uint32Array(typedArray.buffer);
      const r = (m_w) => {
        let m_z = 987654321;
        const mask = 4294967295;
        return function() {
          m_z = 36969 * (m_z & 65535) + (m_z >> 16) & mask;
          m_w = 18e3 * (m_w & 65535) + (m_w >> 16) & mask;
          const result = ((m_z << 16) + m_w & mask) / 4294967296 + 0.5;
          return result * (Math.random() > 0.5 ? 1 : -1);
        };
      };
      for (let i = 0, rcache; i < typedArray.length; i += 4) {
        const _r = r((rcache || Math.random()) * 4294967296);
        rcache = _r() * 987654071;
        words[i / 4] = _r() * 4294967296 | 0;
      }
      return typedArray;
    }
  };
  var mode = {};
  mode.ctrGladman = class {
    constructor(prf, iv) {
      this._prf = prf;
      this._initIv = iv;
      this._iv = iv;
    }
    reset() {
      this._iv = this._initIv;
    }
    /** Input some data to calculate.
     * @param {bitArray} data the data to process, it must be intergral multiple of 128 bits unless it's the last.
     */
    update(data) {
      return this.calculate(this._prf, data, this._iv);
    }
    incWord(word) {
      if ((word >> 24 & 255) === 255) {
        let b1 = word >> 16 & 255;
        let b2 = word >> 8 & 255;
        let b3 = word & 255;
        if (b1 === 255) {
          b1 = 0;
          if (b2 === 255) {
            b2 = 0;
            if (b3 === 255) {
              b3 = 0;
            } else {
              ++b3;
            }
          } else {
            ++b2;
          }
        } else {
          ++b1;
        }
        word = 0;
        word += b1 << 16;
        word += b2 << 8;
        word += b3;
      } else {
        word += 1 << 24;
      }
      return word;
    }
    incCounter(counter) {
      if ((counter[0] = this.incWord(counter[0])) === 0) {
        counter[1] = this.incWord(counter[1]);
      }
    }
    calculate(prf, data, iv) {
      let l;
      if (!(l = data.length)) {
        return [];
      }
      const bl = bitArray.bitLength(data);
      for (let i = 0; i < l; i += 4) {
        this.incCounter(iv);
        const e2 = prf.encrypt(iv);
        data[i] ^= e2[0];
        data[i + 1] ^= e2[1];
        data[i + 2] ^= e2[2];
        data[i + 3] ^= e2[3];
      }
      return bitArray.clamp(data, bl);
    }
  };
  var misc = {
    importKey(password) {
      return new misc.hmacSha1(codec.bytes.toBits(password));
    },
    pbkdf2(prf, salt, count, length) {
      count = count || 1e4;
      if (length < 0 || count < 0) {
        throw new Error("invalid params to pbkdf2");
      }
      const byteLength = (length >> 5) + 1 << 2;
      let u, ui, i, j, k;
      const arrayBuffer = new ArrayBuffer(byteLength);
      const out = new DataView(arrayBuffer);
      let outLength = 0;
      const b = bitArray;
      salt = codec.bytes.toBits(salt);
      for (k = 1; outLength < (byteLength || 1); k++) {
        u = ui = prf.encrypt(b.concat(salt, [k]));
        for (i = 1; i < count; i++) {
          ui = prf.encrypt(ui);
          for (j = 0; j < ui.length; j++) {
            u[j] ^= ui[j];
          }
        }
        for (i = 0; outLength < (byteLength || 1) && i < u.length; i++) {
          out.setInt32(outLength, u[i]);
          outLength += 4;
        }
      }
      return arrayBuffer.slice(0, length / 8);
    }
  };
  misc.hmacSha1 = class {
    constructor(key) {
      const hmac = this;
      const Hash = hmac._hash = hash.sha1;
      const exKey = [[], []];
      hmac._baseHash = [new Hash(), new Hash()];
      const bs = hmac._baseHash[0].blockSize / 32;
      if (key.length > bs) {
        key = new Hash().update(key).finalize();
      }
      for (let i = 0; i < bs; i++) {
        exKey[0][i] = key[i] ^ 909522486;
        exKey[1][i] = key[i] ^ 1549556828;
      }
      hmac._baseHash[0].update(exKey[0]);
      hmac._baseHash[1].update(exKey[1]);
      hmac._resultHash = new Hash(hmac._baseHash[0]);
    }
    reset() {
      const hmac = this;
      hmac._resultHash = new hmac._hash(hmac._baseHash[0]);
      hmac._updated = false;
    }
    update(data) {
      const hmac = this;
      hmac._updated = true;
      hmac._resultHash.update(data);
    }
    digest() {
      const hmac = this;
      const w = hmac._resultHash.finalize();
      const result = new hmac._hash(hmac._baseHash[1]).update(w).finalize();
      hmac.reset();
      return result;
    }
    encrypt(data) {
      if (!this._updated) {
        this.update(data);
        return this.digest(data);
      } else {
        throw new Error("encrypt on already updated hmac called!");
      }
    }
  };

  // lib/zipjs/lib/core/streams/common-crypto.js
  var GET_RANDOM_VALUES_SUPPORTED = typeof crypto != UNDEFINED_TYPE && typeof crypto.getRandomValues == FUNCTION_TYPE;
  var ERR_INVALID_PASSWORD = "Invalid password";
  var ERR_INVALID_SIGNATURE = "Invalid signature";
  var ERR_ABORT_CHECK_PASSWORD = "zipjs-abort-check-password";
  function getRandomValues(array) {
    if (GET_RANDOM_VALUES_SUPPORTED) {
      return crypto.getRandomValues(array);
    } else {
      return random.getRandomValues(array);
    }
  }

  // lib/zipjs/lib/core/streams/aes-crypto-stream.js
  var BLOCK_LENGTH = 16;
  var RAW_FORMAT = "raw";
  var PBKDF2_ALGORITHM = { name: "PBKDF2" };
  var HASH_ALGORITHM = { name: "HMAC" };
  var HASH_FUNCTION = "SHA-1";
  var BASE_KEY_ALGORITHM = Object.assign({ hash: HASH_ALGORITHM }, PBKDF2_ALGORITHM);
  var DERIVED_BITS_ALGORITHM = Object.assign({ iterations: 1e3, hash: { name: HASH_FUNCTION } }, PBKDF2_ALGORITHM);
  var DERIVED_BITS_USAGE = ["deriveBits"];
  var SALT_LENGTH = [8, 12, 16];
  var KEY_LENGTH = [16, 24, 32];
  var SIGNATURE_LENGTH = 10;
  var COUNTER_DEFAULT_VALUE = [0, 0, 0, 0];
  var CRYPTO_API_SUPPORTED = typeof crypto != UNDEFINED_TYPE;
  var subtle = CRYPTO_API_SUPPORTED && crypto.subtle;
  var SUBTLE_API_SUPPORTED = CRYPTO_API_SUPPORTED && typeof subtle != UNDEFINED_TYPE;
  var codecBytes = codec.bytes;
  var Aes = cipher.aes;
  var CtrGladman = mode.ctrGladman;
  var HmacSha1 = misc.hmacSha1;
  var IMPORT_KEY_SUPPORTED = CRYPTO_API_SUPPORTED && SUBTLE_API_SUPPORTED && typeof subtle.importKey == FUNCTION_TYPE;
  var DERIVE_BITS_SUPPORTED = CRYPTO_API_SUPPORTED && SUBTLE_API_SUPPORTED && typeof subtle.deriveBits == FUNCTION_TYPE;
  var AESDecryptionStream = class extends TransformStream {
    constructor({ password, rawPassword, signed, encryptionStrength, checkPasswordOnly }) {
      super({
        start() {
          Object.assign(this, {
            ready: new Promise((resolve) => this.resolveReady = resolve),
            password: encodePassword(password, rawPassword),
            signed,
            strength: encryptionStrength - 1,
            pending: new Uint8Array()
          });
        },
        async transform(chunk, controller) {
          const aesCrypto = this;
          const {
            password: password2,
            strength,
            resolveReady,
            ready
          } = aesCrypto;
          if (password2) {
            await createDecryptionKeys(aesCrypto, strength, password2, subarray(chunk, 0, SALT_LENGTH[strength] + 2));
            chunk = subarray(chunk, SALT_LENGTH[strength] + 2);
            if (checkPasswordOnly) {
              controller.error(new Error(ERR_ABORT_CHECK_PASSWORD));
            } else {
              resolveReady();
            }
          } else {
            await ready;
          }
          const output = new Uint8Array(chunk.length - SIGNATURE_LENGTH - (chunk.length - SIGNATURE_LENGTH) % BLOCK_LENGTH);
          controller.enqueue(append(aesCrypto, chunk, output, 0, SIGNATURE_LENGTH, true));
        },
        async flush(controller) {
          const {
            signed: signed2,
            ctr,
            hmac,
            pending,
            ready
          } = this;
          if (hmac && ctr) {
            await ready;
            const chunkToDecrypt = subarray(pending, 0, pending.length - SIGNATURE_LENGTH);
            const originalSignature = subarray(pending, pending.length - SIGNATURE_LENGTH);
            let decryptedChunkArray = new Uint8Array();
            if (chunkToDecrypt.length) {
              const encryptedChunk = toBits(codecBytes, chunkToDecrypt);
              hmac.update(encryptedChunk);
              const decryptedChunk = ctr.update(encryptedChunk);
              decryptedChunkArray = fromBits(codecBytes, decryptedChunk);
            }
            if (signed2) {
              const signature = subarray(fromBits(codecBytes, hmac.digest()), 0, SIGNATURE_LENGTH);
              for (let indexSignature = 0; indexSignature < SIGNATURE_LENGTH; indexSignature++) {
                if (signature[indexSignature] != originalSignature[indexSignature]) {
                  throw new Error(ERR_INVALID_SIGNATURE);
                }
              }
            }
            controller.enqueue(decryptedChunkArray);
          }
        }
      });
    }
  };
  var AESEncryptionStream = class extends TransformStream {
    constructor({ password, rawPassword, encryptionStrength }) {
      let stream;
      super({
        start() {
          Object.assign(this, {
            ready: new Promise((resolve) => this.resolveReady = resolve),
            password: encodePassword(password, rawPassword),
            strength: encryptionStrength - 1,
            pending: new Uint8Array()
          });
        },
        async transform(chunk, controller) {
          const aesCrypto = this;
          const {
            password: password2,
            strength,
            resolveReady,
            ready
          } = aesCrypto;
          let preamble = new Uint8Array();
          if (password2) {
            preamble = await createEncryptionKeys(aesCrypto, strength, password2);
            resolveReady();
          } else {
            await ready;
          }
          const output = new Uint8Array(preamble.length + chunk.length - chunk.length % BLOCK_LENGTH);
          output.set(preamble, 0);
          controller.enqueue(append(aesCrypto, chunk, output, preamble.length, 0));
        },
        async flush(controller) {
          const {
            ctr,
            hmac,
            pending,
            ready
          } = this;
          if (hmac && ctr) {
            await ready;
            let encryptedChunkArray = new Uint8Array();
            if (pending.length) {
              const encryptedChunk = ctr.update(toBits(codecBytes, pending));
              hmac.update(encryptedChunk);
              encryptedChunkArray = fromBits(codecBytes, encryptedChunk);
            }
            stream.signature = fromBits(codecBytes, hmac.digest()).slice(0, SIGNATURE_LENGTH);
            controller.enqueue(concat(encryptedChunkArray, stream.signature));
          }
        }
      });
      stream = this;
    }
  };
  function append(aesCrypto, input, output, paddingStart, paddingEnd, verifySignature) {
    const {
      ctr,
      hmac,
      pending
    } = aesCrypto;
    const inputLength = input.length - paddingEnd;
    if (pending.length) {
      input = concat(pending, input);
      output = expand(output, inputLength - inputLength % BLOCK_LENGTH);
    }
    let offset;
    for (offset = 0; offset <= inputLength - BLOCK_LENGTH; offset += BLOCK_LENGTH) {
      const inputChunk = toBits(codecBytes, subarray(input, offset, offset + BLOCK_LENGTH));
      if (verifySignature) {
        hmac.update(inputChunk);
      }
      const outputChunk = ctr.update(inputChunk);
      if (!verifySignature) {
        hmac.update(outputChunk);
      }
      output.set(fromBits(codecBytes, outputChunk), offset + paddingStart);
    }
    aesCrypto.pending = subarray(input, offset);
    return output;
  }
  async function createDecryptionKeys(decrypt2, strength, password, preamble) {
    const passwordVerificationKey = await createKeys(decrypt2, strength, password, subarray(preamble, 0, SALT_LENGTH[strength]));
    const passwordVerification = subarray(preamble, SALT_LENGTH[strength]);
    if (passwordVerificationKey[0] != passwordVerification[0] || passwordVerificationKey[1] != passwordVerification[1]) {
      throw new Error(ERR_INVALID_PASSWORD);
    }
  }
  async function createEncryptionKeys(encrypt2, strength, password) {
    const salt = getRandomValues(new Uint8Array(SALT_LENGTH[strength]));
    const passwordVerification = await createKeys(encrypt2, strength, password, salt);
    return concat(salt, passwordVerification);
  }
  async function createKeys(aesCrypto, strength, password, salt) {
    aesCrypto.password = null;
    const baseKey = await importKey(RAW_FORMAT, password, BASE_KEY_ALGORITHM, false, DERIVED_BITS_USAGE);
    const derivedBits = await deriveBits(Object.assign({ salt }, DERIVED_BITS_ALGORITHM), baseKey, 8 * (KEY_LENGTH[strength] * 2 + 2));
    const compositeKey = new Uint8Array(derivedBits);
    const key = toBits(codecBytes, subarray(compositeKey, 0, KEY_LENGTH[strength]));
    const authentication = toBits(codecBytes, subarray(compositeKey, KEY_LENGTH[strength], KEY_LENGTH[strength] * 2));
    const passwordVerification = subarray(compositeKey, KEY_LENGTH[strength] * 2);
    Object.assign(aesCrypto, {
      keys: {
        key,
        authentication,
        passwordVerification
      },
      ctr: new CtrGladman(new Aes(key), Array.from(COUNTER_DEFAULT_VALUE)),
      hmac: new HmacSha1(authentication)
    });
    return passwordVerification;
  }
  async function importKey(format, password, algorithm, extractable, keyUsages) {
    if (IMPORT_KEY_SUPPORTED) {
      try {
        return await subtle.importKey(format, password, algorithm, extractable, keyUsages);
      } catch (_error) {
        IMPORT_KEY_SUPPORTED = false;
        return misc.importKey(password);
      }
    } else {
      return misc.importKey(password);
    }
  }
  async function deriveBits(algorithm, baseKey, length) {
    if (DERIVE_BITS_SUPPORTED) {
      try {
        return await subtle.deriveBits(algorithm, baseKey, length);
      } catch (_error) {
        DERIVE_BITS_SUPPORTED = false;
        return misc.pbkdf2(baseKey, algorithm.salt, DERIVED_BITS_ALGORITHM.iterations, length);
      }
    } else {
      return misc.pbkdf2(baseKey, algorithm.salt, DERIVED_BITS_ALGORITHM.iterations, length);
    }
  }
  function encodePassword(password, rawPassword) {
    if (rawPassword === UNDEFINED_VALUE) {
      return encodeText(password);
    } else {
      return rawPassword;
    }
  }
  function concat(leftArray, rightArray) {
    let array = leftArray;
    if (leftArray.length + rightArray.length) {
      array = new Uint8Array(leftArray.length + rightArray.length);
      array.set(leftArray, 0);
      array.set(rightArray, leftArray.length);
    }
    return array;
  }
  function expand(inputArray, length) {
    if (length && length > inputArray.length) {
      const array = inputArray;
      inputArray = new Uint8Array(length);
      inputArray.set(array, 0);
    }
    return inputArray;
  }
  function subarray(array, begin, end) {
    return array.subarray(begin, end);
  }
  function fromBits(codecBytes2, chunk) {
    return codecBytes2.fromBits(chunk);
  }
  function toBits(codecBytes2, chunk) {
    return codecBytes2.toBits(chunk);
  }

  // lib/zipjs/lib/core/streams/zip-crypto-stream.js
  var HEADER_LENGTH = 12;
  var ZipCryptoDecryptionStream = class extends TransformStream {
    constructor({ password, passwordVerification, checkPasswordOnly }) {
      super({
        start() {
          Object.assign(this, {
            password,
            passwordVerification
          });
          createKeys2(this, password);
        },
        transform(chunk, controller) {
          const zipCrypto = this;
          if (zipCrypto.password) {
            const decryptedHeader = decrypt(zipCrypto, chunk.subarray(0, HEADER_LENGTH));
            zipCrypto.password = null;
            if (decryptedHeader[HEADER_LENGTH - 1] != zipCrypto.passwordVerification) {
              throw new Error(ERR_INVALID_PASSWORD);
            }
            chunk = chunk.subarray(HEADER_LENGTH);
          }
          if (checkPasswordOnly) {
            controller.error(new Error(ERR_ABORT_CHECK_PASSWORD));
          } else {
            controller.enqueue(decrypt(zipCrypto, chunk));
          }
        }
      });
    }
  };
  var ZipCryptoEncryptionStream = class extends TransformStream {
    constructor({ password, passwordVerification }) {
      super({
        start() {
          Object.assign(this, {
            password,
            passwordVerification
          });
          createKeys2(this, password);
        },
        transform(chunk, controller) {
          const zipCrypto = this;
          let output;
          let offset;
          if (zipCrypto.password) {
            zipCrypto.password = null;
            const header = getRandomValues(new Uint8Array(HEADER_LENGTH));
            header[HEADER_LENGTH - 1] = zipCrypto.passwordVerification;
            output = new Uint8Array(chunk.length + header.length);
            output.set(encrypt(zipCrypto, header), 0);
            offset = HEADER_LENGTH;
          } else {
            output = new Uint8Array(chunk.length);
            offset = 0;
          }
          output.set(encrypt(zipCrypto, chunk), offset);
          controller.enqueue(output);
        }
      });
    }
  };
  function decrypt(target, input) {
    const output = new Uint8Array(input.length);
    for (let index = 0; index < input.length; index++) {
      output[index] = getByte(target) ^ input[index];
      updateKeys(target, output[index]);
    }
    return output;
  }
  function encrypt(target, input) {
    const output = new Uint8Array(input.length);
    for (let index = 0; index < input.length; index++) {
      output[index] = getByte(target) ^ input[index];
      updateKeys(target, input[index]);
    }
    return output;
  }
  function createKeys2(target, password) {
    const keys = [305419896, 591751049, 878082192];
    Object.assign(target, {
      keys,
      crcKey0: new Crc32(keys[0]),
      crcKey2: new Crc32(keys[2])
    });
    for (let index = 0; index < password.length; index++) {
      updateKeys(target, password.charCodeAt(index));
    }
  }
  function updateKeys(target, byte) {
    let [key0, key1, key2] = target.keys;
    target.crcKey0.append([byte]);
    key0 = ~target.crcKey0.get();
    key1 = getInt32(Math.imul(getInt32(key1 + getInt8(key0)), 134775813) + 1);
    target.crcKey2.append([key1 >>> 24]);
    key2 = ~target.crcKey2.get();
    target.keys = [key0, key1, key2];
  }
  function getByte(target) {
    const temp = target.keys[2] | 2;
    return getInt8(Math.imul(temp, temp ^ 1) >>> 8);
  }
  function getInt8(number) {
    return number & 255;
  }
  function getInt32(number) {
    return number & 4294967295;
  }

  // lib/zipjs/lib/core/streams/zip-entry-stream.js
  var COMPRESSION_FORMAT = "deflate-raw";
  var DeflateStream = class extends TransformStream {
    constructor(options, { chunkSize, CompressionStream: CompressionStream2, CompressionStreamNative }) {
      super({});
      const { compressed, encrypted, useCompressionStream, zipCrypto, signed, level } = options;
      const stream = this;
      let crc32Stream, encryptionStream;
      let readable = filterEmptyChunks(super.readable);
      if ((!encrypted || zipCrypto) && signed) {
        crc32Stream = new Crc32Stream();
        readable = pipeThrough(readable, crc32Stream);
      }
      if (compressed) {
        readable = pipeThroughCommpressionStream(readable, useCompressionStream, { level, chunkSize }, CompressionStreamNative, CompressionStream2);
      }
      if (encrypted) {
        if (zipCrypto) {
          readable = pipeThrough(readable, new ZipCryptoEncryptionStream(options));
        } else {
          encryptionStream = new AESEncryptionStream(options);
          readable = pipeThrough(readable, encryptionStream);
        }
      }
      setReadable(stream, readable, () => {
        let signature;
        if (encrypted && !zipCrypto) {
          signature = encryptionStream.signature;
        }
        if ((!encrypted || zipCrypto) && signed) {
          signature = new DataView(crc32Stream.value.buffer).getUint32(0);
        }
        stream.signature = signature;
      });
    }
  };
  var InflateStream = class extends TransformStream {
    constructor(options, { chunkSize, DecompressionStream: DecompressionStream2, DecompressionStreamNative }) {
      super({});
      const { zipCrypto, encrypted, signed, signature, compressed, useCompressionStream } = options;
      let crc32Stream, decryptionStream;
      let readable = filterEmptyChunks(super.readable);
      if (encrypted) {
        if (zipCrypto) {
          readable = pipeThrough(readable, new ZipCryptoDecryptionStream(options));
        } else {
          decryptionStream = new AESDecryptionStream(options);
          readable = pipeThrough(readable, decryptionStream);
        }
      }
      if (compressed) {
        readable = pipeThroughCommpressionStream(readable, useCompressionStream, { chunkSize }, DecompressionStreamNative, DecompressionStream2);
      }
      if ((!encrypted || zipCrypto) && signed) {
        crc32Stream = new Crc32Stream();
        readable = pipeThrough(readable, crc32Stream);
      }
      setReadable(this, readable, () => {
        if ((!encrypted || zipCrypto) && signed) {
          const dataViewSignature = new DataView(crc32Stream.value.buffer);
          if (signature != dataViewSignature.getUint32(0, false)) {
            throw new Error(ERR_INVALID_SIGNATURE);
          }
        }
      });
    }
  };
  function filterEmptyChunks(readable) {
    return pipeThrough(readable, new TransformStream({
      transform(chunk, controller) {
        if (chunk && chunk.length) {
          controller.enqueue(chunk);
        }
      }
    }));
  }
  function setReadable(stream, readable, flush) {
    readable = pipeThrough(readable, new TransformStream({ flush }));
    Object.defineProperty(stream, "readable", {
      get() {
        return readable;
      }
    });
  }
  function pipeThroughCommpressionStream(readable, useCompressionStream, options, CodecStreamNative, CodecStream2) {
    try {
      const CompressionStream2 = useCompressionStream && CodecStreamNative ? CodecStreamNative : CodecStream2;
      readable = pipeThrough(readable, new CompressionStream2(COMPRESSION_FORMAT, options));
    } catch (_error) {
      if (useCompressionStream) {
        try {
          readable = pipeThrough(readable, new CodecStream2(COMPRESSION_FORMAT, options));
        } catch (_error2) {
          return readable;
        }
      } else {
        return readable;
      }
    }
    return readable;
  }
  function pipeThrough(readable, transformStream) {
    return readable.pipeThrough(transformStream);
  }

  // lib/zipjs/lib/core/streams/codec-stream.js
  var MESSAGE_EVENT_TYPE = "message";
  var MESSAGE_START = "start";
  var MESSAGE_PULL = "pull";
  var MESSAGE_DATA = "data";
  var MESSAGE_ACK_DATA = "ack";
  var MESSAGE_CLOSE = "close";
  var CODEC_DEFLATE = "deflate";
  var CODEC_INFLATE = "inflate";
  var CodecStream = class extends TransformStream {
    constructor(options, config3) {
      super({});
      const codec2 = this;
      const { codecType } = options;
      let Stream2;
      if (codecType.startsWith(CODEC_DEFLATE)) {
        Stream2 = DeflateStream;
      } else if (codecType.startsWith(CODEC_INFLATE)) {
        Stream2 = InflateStream;
      }
      let outputSize = 0;
      let inputSize = 0;
      const stream = new Stream2(options, config3);
      const readable = super.readable;
      const inputSizeStream = new TransformStream({
        transform(chunk, controller) {
          if (chunk && chunk.length) {
            inputSize += chunk.length;
            controller.enqueue(chunk);
          }
        },
        flush() {
          Object.assign(codec2, {
            inputSize
          });
        }
      });
      const outputSizeStream = new TransformStream({
        transform(chunk, controller) {
          if (chunk && chunk.length) {
            outputSize += chunk.length;
            controller.enqueue(chunk);
          }
        },
        flush() {
          const { signature } = stream;
          Object.assign(codec2, {
            signature,
            outputSize,
            inputSize
          });
        }
      });
      Object.defineProperty(codec2, "readable", {
        get() {
          return readable.pipeThrough(inputSizeStream).pipeThrough(stream).pipeThrough(outputSizeStream);
        }
      });
    }
  };
  var ChunkStream = class extends TransformStream {
    constructor(chunkSize) {
      let pendingChunk;
      super({
        transform,
        flush(controller) {
          if (pendingChunk && pendingChunk.length) {
            controller.enqueue(pendingChunk);
          }
        }
      });
      function transform(chunk, controller) {
        if (pendingChunk) {
          const newChunk = new Uint8Array(pendingChunk.length + chunk.length);
          newChunk.set(pendingChunk);
          newChunk.set(chunk, pendingChunk.length);
          chunk = newChunk;
          pendingChunk = null;
        }
        if (chunk.length > chunkSize) {
          controller.enqueue(chunk.slice(0, chunkSize));
          transform(chunk.slice(chunkSize), controller);
        } else {
          pendingChunk = chunk;
        }
      }
    }
  };

  // lib/zipjs/lib/core/codec-worker.js
  var WEB_WORKERS_SUPPORTED = typeof Worker != UNDEFINED_TYPE;
  var CodecWorker = class {
    constructor(workerData, { readable, writable }, { options, config: config3, streamOptions, useWebWorkers, transferStreams, scripts }, onTaskFinished) {
      const { signal } = streamOptions;
      Object.assign(workerData, {
        busy: true,
        readable: readable.pipeThrough(new ChunkStream(config3.chunkSize)).pipeThrough(new ProgressWatcherStream(readable, streamOptions), { signal }),
        writable,
        options: Object.assign({}, options),
        scripts,
        transferStreams,
        terminate() {
          return new Promise((resolve) => {
            const { worker, busy } = workerData;
            if (worker) {
              if (busy) {
                workerData.resolveTerminated = resolve;
              } else {
                worker.terminate();
                resolve();
              }
              workerData.interface = null;
            } else {
              resolve();
            }
          });
        },
        onTaskFinished() {
          const { resolveTerminated } = workerData;
          if (resolveTerminated) {
            workerData.resolveTerminated = null;
            workerData.terminated = true;
            workerData.worker.terminate();
            resolveTerminated();
          }
          workerData.busy = false;
          onTaskFinished(workerData);
        }
      });
      return (useWebWorkers && WEB_WORKERS_SUPPORTED ? createWebWorkerInterface : createWorkerInterface)(workerData, config3);
    }
  };
  var ProgressWatcherStream = class extends TransformStream {
    constructor(readableSource, { onstart, onprogress, size, onend }) {
      let chunkOffset = 0;
      super({
        async start() {
          if (onstart) {
            await callHandler(onstart, size);
          }
        },
        async transform(chunk, controller) {
          chunkOffset += chunk.length;
          if (onprogress) {
            await callHandler(onprogress, chunkOffset, size);
          }
          controller.enqueue(chunk);
        },
        async flush() {
          readableSource.size = chunkOffset;
          if (onend) {
            await callHandler(onend, chunkOffset);
          }
        }
      });
    }
  };
  async function callHandler(handler, ...parameters) {
    try {
      await handler(...parameters);
    } catch (_error) {
    }
  }
  function createWorkerInterface(workerData, config3) {
    return {
      run: () => runWorker(workerData, config3)
    };
  }
  function createWebWorkerInterface(workerData, config3) {
    const { baseURL: baseURL2, chunkSize } = config3;
    if (!workerData.interface) {
      let worker;
      try {
        worker = getWebWorker(workerData.scripts[0], baseURL2, workerData);
      } catch (_error) {
        WEB_WORKERS_SUPPORTED = false;
        return createWorkerInterface(workerData, config3);
      }
      Object.assign(workerData, {
        worker,
        interface: {
          run: () => runWebWorker(workerData, { chunkSize })
        }
      });
    }
    return workerData.interface;
  }
  async function runWorker({ options, readable, writable, onTaskFinished }, config3) {
    try {
      const codecStream = new CodecStream(options, config3);
      await readable.pipeThrough(codecStream).pipeTo(writable, { preventClose: true, preventAbort: true });
      const {
        signature,
        inputSize,
        outputSize
      } = codecStream;
      return {
        signature,
        inputSize,
        outputSize
      };
    } finally {
      onTaskFinished();
    }
  }
  async function runWebWorker(workerData, config3) {
    let resolveResult, rejectResult;
    const result = new Promise((resolve, reject) => {
      resolveResult = resolve;
      rejectResult = reject;
    });
    Object.assign(workerData, {
      reader: null,
      writer: null,
      resolveResult,
      rejectResult,
      result
    });
    const { readable, options, scripts } = workerData;
    const { writable, closed } = watchClosedStream(workerData.writable);
    const streamsTransferred = sendMessage({
      type: MESSAGE_START,
      scripts: scripts.slice(1),
      options,
      config: config3,
      readable,
      writable
    }, workerData);
    if (!streamsTransferred) {
      Object.assign(workerData, {
        reader: readable.getReader(),
        writer: writable.getWriter()
      });
    }
    const resultValue = await result;
    if (!streamsTransferred) {
      await writable.getWriter().close();
    }
    await closed;
    return resultValue;
  }
  function watchClosedStream(writableSource) {
    let resolveStreamClosed;
    const closed = new Promise((resolve) => resolveStreamClosed = resolve);
    const writable = new WritableStream({
      async write(chunk) {
        const writer = writableSource.getWriter();
        await writer.ready;
        await writer.write(chunk);
        writer.releaseLock();
      },
      close() {
        resolveStreamClosed();
      },
      abort(reason) {
        const writer = writableSource.getWriter();
        return writer.abort(reason);
      }
    });
    return { writable, closed };
  }
  var classicWorkersSupported = true;
  var transferStreamsSupported = true;
  function getWebWorker(url, baseURL2, workerData) {
    const workerOptions = { type: "module" };
    let scriptUrl, worker;
    if (typeof url == FUNCTION_TYPE) {
      url = url();
    }
    try {
      scriptUrl = new URL(url, baseURL2);
    } catch (_error) {
      scriptUrl = url;
    }
    if (classicWorkersSupported) {
      try {
        worker = new Worker(scriptUrl);
      } catch (_error) {
        classicWorkersSupported = false;
        worker = new Worker(scriptUrl, workerOptions);
      }
    } else {
      worker = new Worker(scriptUrl, workerOptions);
    }
    worker.addEventListener(MESSAGE_EVENT_TYPE, (event) => onMessage(event, workerData));
    return worker;
  }
  function sendMessage(message, { worker, writer, onTaskFinished, transferStreams }) {
    try {
      const { value, readable, writable } = message;
      const transferables = [];
      if (value) {
        if (value.byteLength < value.buffer.byteLength) {
          message.value = value.buffer.slice(0, value.byteLength);
        } else {
          message.value = value.buffer;
        }
        transferables.push(message.value);
      }
      if (transferStreams && transferStreamsSupported) {
        if (readable) {
          transferables.push(readable);
        }
        if (writable) {
          transferables.push(writable);
        }
      } else {
        message.readable = message.writable = null;
      }
      if (transferables.length) {
        try {
          worker.postMessage(message, transferables);
          return true;
        } catch (_error) {
          transferStreamsSupported = false;
          message.readable = message.writable = null;
          worker.postMessage(message);
        }
      } else {
        worker.postMessage(message);
      }
    } catch (error) {
      if (writer) {
        writer.releaseLock();
      }
      onTaskFinished();
      throw error;
    }
  }
  async function onMessage({ data }, workerData) {
    const { type, value, messageId, result, error } = data;
    const { reader, writer, resolveResult, rejectResult, onTaskFinished } = workerData;
    try {
      if (error) {
        const { message, stack, code: code2, name } = error;
        const responseError = new Error(message);
        Object.assign(responseError, { stack, code: code2, name });
        close(responseError);
      } else {
        if (type == MESSAGE_PULL) {
          const { value: value2, done } = await reader.read();
          sendMessage({ type: MESSAGE_DATA, value: value2, done, messageId }, workerData);
        }
        if (type == MESSAGE_DATA) {
          await writer.ready;
          await writer.write(new Uint8Array(value));
          sendMessage({ type: MESSAGE_ACK_DATA, messageId }, workerData);
        }
        if (type == MESSAGE_CLOSE) {
          close(null, result);
        }
      }
    } catch (error2) {
      sendMessage({ type: MESSAGE_CLOSE, messageId }, workerData);
      close(error2);
    }
    function close(error2, result2) {
      if (error2) {
        rejectResult(error2);
      } else {
        resolveResult(result2);
      }
      if (writer) {
        writer.releaseLock();
      }
      onTaskFinished();
    }
  }

  // lib/zipjs/lib/core/codec-pool.js
  var pool = [];
  var pendingRequests = [];
  var indexWorker = 0;
  async function runWorker2(stream, workerOptions) {
    const { options, config: config3 } = workerOptions;
    const { transferStreams, useWebWorkers, useCompressionStream, codecType, compressed, signed, encrypted } = options;
    const { workerScripts, maxWorkers: maxWorkers2 } = config3;
    workerOptions.transferStreams = transferStreams || transferStreams === UNDEFINED_VALUE;
    const streamCopy = !compressed && !signed && !encrypted && !workerOptions.transferStreams;
    workerOptions.useWebWorkers = !streamCopy && (useWebWorkers || useWebWorkers === UNDEFINED_VALUE && config3.useWebWorkers);
    workerOptions.scripts = workerOptions.useWebWorkers && workerScripts ? workerScripts[codecType] : [];
    options.useCompressionStream = useCompressionStream || useCompressionStream === UNDEFINED_VALUE && config3.useCompressionStream;
    return (await getWorker()).run();
    async function getWorker() {
      const workerData = pool.find((workerData2) => !workerData2.busy);
      if (workerData) {
        clearTerminateTimeout(workerData);
        return new CodecWorker(workerData, stream, workerOptions, onTaskFinished);
      } else if (pool.length < maxWorkers2) {
        const workerData2 = { indexWorker };
        indexWorker++;
        pool.push(workerData2);
        return new CodecWorker(workerData2, stream, workerOptions, onTaskFinished);
      } else {
        return new Promise((resolve) => pendingRequests.push({ resolve, stream, workerOptions }));
      }
    }
    function onTaskFinished(workerData) {
      if (pendingRequests.length) {
        const [{ resolve, stream: stream2, workerOptions: workerOptions2 }] = pendingRequests.splice(0, 1);
        resolve(new CodecWorker(workerData, stream2, workerOptions2, onTaskFinished));
      } else if (workerData.worker) {
        clearTerminateTimeout(workerData);
        terminateWorker(workerData, workerOptions);
      } else {
        pool = pool.filter((data) => data != workerData);
      }
    }
  }
  function terminateWorker(workerData, workerOptions) {
    const { config: config3 } = workerOptions;
    const { terminateWorkerTimeout } = config3;
    if (Number.isFinite(terminateWorkerTimeout) && terminateWorkerTimeout >= 0) {
      if (workerData.terminated) {
        workerData.terminated = false;
      } else {
        workerData.terminateTimeout = setTimeout(async () => {
          pool = pool.filter((data) => data != workerData);
          try {
            await workerData.terminate();
          } catch (_error) {
          }
        }, terminateWorkerTimeout);
      }
    }
  }
  function clearTerminateTimeout(workerData) {
    const { terminateTimeout } = workerData;
    if (terminateTimeout) {
      clearTimeout(terminateTimeout);
      workerData.terminateTimeout = null;
    }
  }

  // lib/zipjs/lib/z-worker-inline.js
  function e(e2, t = {}) {
    const n = 'const{Array:e,Object:t,Number:n,Math:r,Error:s,Uint8Array:i,Uint16Array:o,Uint32Array:c,Int32Array:f,Map:a,DataView:l,Promise:u,TextEncoder:w,crypto:h,postMessage:d,TransformStream:p,ReadableStream:y,WritableStream:m,CompressionStream:b,DecompressionStream:g}=self,k=void 0,v="undefined",S="function";class z{constructor(e){return class extends p{constructor(t,n){const r=new e(n);super({transform(e,t){t.enqueue(r.append(e))},flush(e){const t=r.flush();t&&e.enqueue(t)}})}}}}const C=[];for(let e=0;256>e;e++){let t=e;for(let e=0;8>e;e++)1&t?t=t>>>1^3988292384:t>>>=1;C[e]=t}class x{constructor(e){this.t=e||-1}append(e){let t=0|this.t;for(let n=0,r=0|e.length;r>n;n++)t=t>>>8^C[255&(t^e[n])];this.t=t}get(){return~this.t}}class A extends p{constructor(){let e;const t=new x;super({transform(e,n){t.append(e),n.enqueue(e)},flush(){const n=new i(4);new l(n.buffer).setUint32(0,t.get()),e.value=n}}),e=this}}const _={concat(e,t){if(0===e.length||0===t.length)return e.concat(t);const n=e[e.length-1],r=_.i(n);return 32===r?e.concat(t):_.o(t,r,0|n,e.slice(0,e.length-1))},l(e){const t=e.length;if(0===t)return 0;const n=e[t-1];return 32*(t-1)+_.i(n)},u(e,t){if(32*e.length<t)return e;const n=(e=e.slice(0,r.ceil(t/32))).length;return t&=31,n>0&&t&&(e[n-1]=_.h(t,e[n-1]&2147483648>>t-1,1)),e},h:(e,t,n)=>32===e?t:(n?0|t:t<<32-e)+1099511627776*e,i:e=>r.round(e/1099511627776)||32,o(e,t,n,r){for(void 0===r&&(r=[]);t>=32;t-=32)r.push(n),n=0;if(0===t)return r.concat(e);for(let s=0;s<e.length;s++)r.push(n|e[s]>>>t),n=e[s]<<32-t;const s=e.length?e[e.length-1]:0,i=_.i(s);return r.push(_.h(t+i&31,t+i>32?n:r.pop(),1)),r}},I={bytes:{p(e){const t=_.l(e)/8,n=new i(t);let r;for(let s=0;t>s;s++)3&s||(r=e[s/4]),n[s]=r>>>24,r<<=8;return n},m(e){const t=[];let n,r=0;for(n=0;n<e.length;n++)r=r<<8|e[n],3&~n||(t.push(r),r=0);return 3&n&&t.push(_.h(8*(3&n),r)),t}}},P=class{constructor(e){const t=this;t.blockSize=512,t.k=[1732584193,4023233417,2562383102,271733878,3285377520],t.v=[1518500249,1859775393,2400959708,3395469782],e?(t.S=e.S.slice(0),t.C=e.C.slice(0),t.A=e.A):t.reset()}reset(){const e=this;return e.S=e.k.slice(0),e.C=[],e.A=0,e}update(e){const t=this;"string"==typeof e&&(e=I._.m(e));const n=t.C=_.concat(t.C,e),r=t.A,i=t.A=r+_.l(e);if(i>9007199254740991)throw new s("Cannot hash more than 2^53 - 1 bits");const o=new c(n);let f=0;for(let e=t.blockSize+r-(t.blockSize+r&t.blockSize-1);i>=e;e+=t.blockSize)t.I(o.subarray(16*f,16*(f+1))),f+=1;return n.splice(0,16*f),t}P(){const e=this;let t=e.C;const n=e.S;t=_.concat(t,[_.h(1,1)]);for(let e=t.length+2;15&e;e++)t.push(0);for(t.push(r.floor(e.A/4294967296)),t.push(0|e.A);t.length;)e.I(t.splice(0,16));return e.reset(),n}D(e,t,n,r){return e>19?e>39?e>59?e>79?void 0:t^n^r:t&n|t&r|n&r:t^n^r:t&n|~t&r}V(e,t){return t<<e|t>>>32-e}I(t){const n=this,s=n.S,i=e(80);for(let e=0;16>e;e++)i[e]=t[e];let o=s[0],c=s[1],f=s[2],a=s[3],l=s[4];for(let e=0;79>=e;e++){16>e||(i[e]=n.V(1,i[e-3]^i[e-8]^i[e-14]^i[e-16]));const t=n.V(5,o)+n.D(e,c,f,a)+l+i[e]+n.v[r.floor(e/20)]|0;l=a,a=f,f=n.V(30,c),c=o,o=t}s[0]=s[0]+o|0,s[1]=s[1]+c|0,s[2]=s[2]+f|0,s[3]=s[3]+a|0,s[4]=s[4]+l|0}},D={getRandomValues(e){const t=new c(e.buffer),n=e=>{let t=987654321;const n=4294967295;return()=>(t=36969*(65535&t)+(t>>16)&n,(((t<<16)+(e=18e3*(65535&e)+(e>>16)&n)&n)/4294967296+.5)*(r.random()>.5?1:-1))};for(let s,i=0;i<e.length;i+=4){const e=n(4294967296*(s||r.random()));s=987654071*e(),t[i/4]=4294967296*e()|0}return e}},V={importKey:e=>new V.R(I.bytes.m(e)),B(e,t,n,r){if(n=n||1e4,0>r||0>n)throw new s("invalid params to pbkdf2");const i=1+(r>>5)<<2;let o,c,f,a,u;const w=new ArrayBuffer(i),h=new l(w);let d=0;const p=_;for(t=I.bytes.m(t),u=1;(i||1)>d;u++){for(o=c=e.encrypt(p.concat(t,[u])),f=1;n>f;f++)for(c=e.encrypt(c),a=0;a<c.length;a++)o[a]^=c[a];for(f=0;(i||1)>d&&f<o.length;f++)h.setInt32(d,o[f]),d+=4}return w.slice(0,r/8)},R:class{constructor(e){const t=this,n=t.M=P,r=[[],[]];t.U=[new n,new n];const s=t.U[0].blockSize/32;e.length>s&&(e=(new n).update(e).P());for(let t=0;s>t;t++)r[0][t]=909522486^e[t],r[1][t]=1549556828^e[t];t.U[0].update(r[0]),t.U[1].update(r[1]),t.K=new n(t.U[0])}reset(){const e=this;e.K=new e.M(e.U[0]),e.N=!1}update(e){this.N=!0,this.K.update(e)}digest(){const e=this,t=e.K.P(),n=new e.M(e.U[1]).update(t).P();return e.reset(),n}encrypt(e){if(this.N)throw new s("encrypt on already updated hmac called!");return this.update(e),this.digest(e)}}},R=typeof h!=v&&typeof h.getRandomValues==S,B="Invalid password",E="Invalid signature",M="zipjs-abort-check-password";function U(e){return R?h.getRandomValues(e):D.getRandomValues(e)}const K=16,N={name:"PBKDF2"},O=t.assign({hash:{name:"HMAC"}},N),T=t.assign({iterations:1e3,hash:{name:"SHA-1"}},N),W=["deriveBits"],j=[8,12,16],H=[16,24,32],L=10,F=[0,0,0,0],q=typeof h!=v,G=q&&h.subtle,J=q&&typeof G!=v,Q=I.bytes,X=class{constructor(e){const t=this;t.O=[[[],[],[],[],[]],[[],[],[],[],[]]],t.O[0][0][0]||t.T();const n=t.O[0][4],r=t.O[1],i=e.length;let o,c,f,a=1;if(4!==i&&6!==i&&8!==i)throw new s("invalid aes key size");for(t.v=[c=e.slice(0),f=[]],o=i;4*i+28>o;o++){let e=c[o-1];(o%i==0||8===i&&o%i==4)&&(e=n[e>>>24]<<24^n[e>>16&255]<<16^n[e>>8&255]<<8^n[255&e],o%i==0&&(e=e<<8^e>>>24^a<<24,a=a<<1^283*(a>>7))),c[o]=c[o-i]^e}for(let e=0;o;e++,o--){const t=c[3&e?o:o-4];f[e]=4>=o||4>e?t:r[0][n[t>>>24]]^r[1][n[t>>16&255]]^r[2][n[t>>8&255]]^r[3][n[255&t]]}}encrypt(e){return this.W(e,0)}decrypt(e){return this.W(e,1)}T(){const e=this.O[0],t=this.O[1],n=e[4],r=t[4],s=[],i=[];let o,c,f,a;for(let e=0;256>e;e++)i[(s[e]=e<<1^283*(e>>7))^e]=e;for(let l=o=0;!n[l];l^=c||1,o=i[o]||1){let i=o^o<<1^o<<2^o<<3^o<<4;i=i>>8^255&i^99,n[l]=i,r[i]=l,a=s[f=s[c=s[l]]];let u=16843009*a^65537*f^257*c^16843008*l,w=257*s[i]^16843008*i;for(let n=0;4>n;n++)e[n][l]=w=w<<24^w>>>8,t[n][i]=u=u<<24^u>>>8}for(let n=0;5>n;n++)e[n]=e[n].slice(0),t[n]=t[n].slice(0)}W(e,t){if(4!==e.length)throw new s("invalid aes block size");const n=this.v[t],r=n.length/4-2,i=[0,0,0,0],o=this.O[t],c=o[0],f=o[1],a=o[2],l=o[3],u=o[4];let w,h,d,p=e[0]^n[0],y=e[t?3:1]^n[1],m=e[2]^n[2],b=e[t?1:3]^n[3],g=4;for(let e=0;r>e;e++)w=c[p>>>24]^f[y>>16&255]^a[m>>8&255]^l[255&b]^n[g],h=c[y>>>24]^f[m>>16&255]^a[b>>8&255]^l[255&p]^n[g+1],d=c[m>>>24]^f[b>>16&255]^a[p>>8&255]^l[255&y]^n[g+2],b=c[b>>>24]^f[p>>16&255]^a[y>>8&255]^l[255&m]^n[g+3],g+=4,p=w,y=h,m=d;for(let e=0;4>e;e++)i[t?3&-e:e]=u[p>>>24]<<24^u[y>>16&255]<<16^u[m>>8&255]<<8^u[255&b]^n[g++],w=p,p=y,y=m,m=b,b=w;return i}},Y=class{constructor(e,t){this.j=e,this.H=t,this.L=t}reset(){this.L=this.H}update(e){return this.F(this.j,e,this.L)}q(e){if(255&~(e>>24))e+=1<<24;else{let t=e>>16&255,n=e>>8&255,r=255&e;255===t?(t=0,255===n?(n=0,255===r?r=0:++r):++n):++t,e=0,e+=t<<16,e+=n<<8,e+=r}return e}G(e){0===(e[0]=this.q(e[0]))&&(e[1]=this.q(e[1]))}F(e,t,n){let r;if(!(r=t.length))return[];const s=_.l(t);for(let s=0;r>s;s+=4){this.G(n);const r=e.encrypt(n);t[s]^=r[0],t[s+1]^=r[1],t[s+2]^=r[2],t[s+3]^=r[3]}return _.u(t,s)}},Z=V.R;let $=q&&J&&typeof G.importKey==S,ee=q&&J&&typeof G.deriveBits==S;class te extends p{constructor({password:e,rawPassword:n,signed:r,encryptionStrength:o,checkPasswordOnly:c}){super({start(){t.assign(this,{ready:new u((e=>this.J=e)),password:ie(e,n),signed:r,X:o-1,pending:new i})},async transform(e,t){const n=this,{password:r,X:o,J:f,ready:a}=n;r?(await(async(e,t,n,r)=>{const i=await se(e,t,n,ce(r,0,j[t])),o=ce(r,j[t]);if(i[0]!=o[0]||i[1]!=o[1])throw new s(B)})(n,o,r,ce(e,0,j[o]+2)),e=ce(e,j[o]+2),c?t.error(new s(M)):f()):await a;const l=new i(e.length-L-(e.length-L)%K);t.enqueue(re(n,e,l,0,L,!0))},async flush(e){const{signed:t,Y:n,Z:r,pending:o,ready:c}=this;if(r&&n){await c;const f=ce(o,0,o.length-L),a=ce(o,o.length-L);let l=new i;if(f.length){const e=ae(Q,f);r.update(e);const t=n.update(e);l=fe(Q,t)}if(t){const e=ce(fe(Q,r.digest()),0,L);for(let t=0;L>t;t++)if(e[t]!=a[t])throw new s(E)}e.enqueue(l)}}})}}class ne extends p{constructor({password:e,rawPassword:n,encryptionStrength:r}){let s;super({start(){t.assign(this,{ready:new u((e=>this.J=e)),password:ie(e,n),X:r-1,pending:new i})},async transform(e,t){const n=this,{password:r,X:s,J:o,ready:c}=n;let f=new i;r?(f=await(async(e,t,n)=>{const r=U(new i(j[t]));return oe(r,await se(e,t,n,r))})(n,s,r),o()):await c;const a=new i(f.length+e.length-e.length%K);a.set(f,0),t.enqueue(re(n,e,a,f.length,0))},async flush(e){const{Y:t,Z:n,pending:r,ready:o}=this;if(n&&t){await o;let c=new i;if(r.length){const e=t.update(ae(Q,r));n.update(e),c=fe(Q,e)}s.signature=fe(Q,n.digest()).slice(0,L),e.enqueue(oe(c,s.signature))}}}),s=this}}function re(e,t,n,r,s,o){const{Y:c,Z:f,pending:a}=e,l=t.length-s;let u;for(a.length&&(t=oe(a,t),n=((e,t)=>{if(t&&t>e.length){const n=e;(e=new i(t)).set(n,0)}return e})(n,l-l%K)),u=0;l-K>=u;u+=K){const e=ae(Q,ce(t,u,u+K));o&&f.update(e);const s=c.update(e);o||f.update(s),n.set(fe(Q,s),u+r)}return e.pending=ce(t,u),n}async function se(n,r,s,o){n.password=null;const c=await(async(e,t,n,r,s)=>{if(!$)return V.importKey(t);try{return await G.importKey("raw",t,n,!1,s)}catch(e){return $=!1,V.importKey(t)}})(0,s,O,0,W),f=await(async(e,t,n)=>{if(!ee)return V.B(t,e.salt,T.iterations,n);try{return await G.deriveBits(e,t,n)}catch(r){return ee=!1,V.B(t,e.salt,T.iterations,n)}})(t.assign({salt:o},T),c,8*(2*H[r]+2)),a=new i(f),l=ae(Q,ce(a,0,H[r])),u=ae(Q,ce(a,H[r],2*H[r])),w=ce(a,2*H[r]);return t.assign(n,{keys:{key:l,$:u,passwordVerification:w},Y:new Y(new X(l),e.from(F)),Z:new Z(u)}),w}function ie(e,t){return t===k?(e=>{if(typeof w==v){const t=new i((e=unescape(encodeURIComponent(e))).length);for(let n=0;n<t.length;n++)t[n]=e.charCodeAt(n);return t}return(new w).encode(e)})(e):t}function oe(e,t){let n=e;return e.length+t.length&&(n=new i(e.length+t.length),n.set(e,0),n.set(t,e.length)),n}function ce(e,t,n){return e.subarray(t,n)}function fe(e,t){return e.p(t)}function ae(e,t){return e.m(t)}class le extends p{constructor({password:e,passwordVerification:n,checkPasswordOnly:r}){super({start(){t.assign(this,{password:e,passwordVerification:n}),de(this,e)},transform(e,t){const n=this;if(n.password){const t=we(n,e.subarray(0,12));if(n.password=null,t[11]!=n.passwordVerification)throw new s(B);e=e.subarray(12)}r?t.error(new s(M)):t.enqueue(we(n,e))}})}}class ue extends p{constructor({password:e,passwordVerification:n}){super({start(){t.assign(this,{password:e,passwordVerification:n}),de(this,e)},transform(e,t){const n=this;let r,s;if(n.password){n.password=null;const t=U(new i(12));t[11]=n.passwordVerification,r=new i(e.length+t.length),r.set(he(n,t),0),s=12}else r=new i(e.length),s=0;r.set(he(n,e),s),t.enqueue(r)}})}}function we(e,t){const n=new i(t.length);for(let r=0;r<t.length;r++)n[r]=ye(e)^t[r],pe(e,n[r]);return n}function he(e,t){const n=new i(t.length);for(let r=0;r<t.length;r++)n[r]=ye(e)^t[r],pe(e,t[r]);return n}function de(e,n){const r=[305419896,591751049,878082192];t.assign(e,{keys:r,ee:new x(r[0]),te:new x(r[2])});for(let t=0;t<n.length;t++)pe(e,n.charCodeAt(t))}function pe(e,t){let[n,s,i]=e.keys;e.ee.append([t]),n=~e.ee.get(),s=be(r.imul(be(s+me(n)),134775813)+1),e.te.append([s>>>24]),i=~e.te.get(),e.keys=[n,s,i]}function ye(e){const t=2|e.keys[2];return me(r.imul(t,1^t)>>>8)}function me(e){return 255&e}function be(e){return 4294967295&e}const ge="deflate-raw";class ke extends p{constructor(e,{chunkSize:t,CompressionStream:n,CompressionStreamNative:r}){super({});const{compressed:s,encrypted:i,useCompressionStream:o,zipCrypto:c,signed:f,level:a}=e,u=this;let w,h,d=Se(super.readable);i&&!c||!f||(w=new A,d=xe(d,w)),s&&(d=Ce(d,o,{level:a,chunkSize:t},r,n)),i&&(c?d=xe(d,new ue(e)):(h=new ne(e),d=xe(d,h))),ze(u,d,(()=>{let e;i&&!c&&(e=h.signature),i&&!c||!f||(e=new l(w.value.buffer).getUint32(0)),u.signature=e}))}}class ve extends p{constructor(e,{chunkSize:t,DecompressionStream:n,DecompressionStreamNative:r}){super({});const{zipCrypto:i,encrypted:o,signed:c,signature:f,compressed:a,useCompressionStream:u}=e;let w,h,d=Se(super.readable);o&&(i?d=xe(d,new le(e)):(h=new te(e),d=xe(d,h))),a&&(d=Ce(d,u,{chunkSize:t},r,n)),o&&!i||!c||(w=new A,d=xe(d,w)),ze(this,d,(()=>{if((!o||i)&&c){const e=new l(w.value.buffer);if(f!=e.getUint32(0,!1))throw new s(E)}}))}}function Se(e){return xe(e,new p({transform(e,t){e&&e.length&&t.enqueue(e)}}))}function ze(e,n,r){n=xe(n,new p({flush:r})),t.defineProperty(e,"readable",{get:()=>n})}function Ce(e,t,n,r,s){try{e=xe(e,new(t&&r?r:s)(ge,n))}catch(r){if(!t)return e;try{e=xe(e,new s(ge,n))}catch(t){return e}}return e}function xe(e,t){return e.pipeThrough(t)}const Ae="data",_e="close";class Ie extends p{constructor(e,n){super({});const r=this,{codecType:s}=e;let i;s.startsWith("deflate")?i=ke:s.startsWith("inflate")&&(i=ve);let o=0,c=0;const f=new i(e,n),a=super.readable,l=new p({transform(e,t){e&&e.length&&(c+=e.length,t.enqueue(e))},flush(){t.assign(r,{inputSize:c})}}),u=new p({transform(e,t){e&&e.length&&(o+=e.length,t.enqueue(e))},flush(){const{signature:e}=f;t.assign(r,{signature:e,outputSize:o,inputSize:c})}});t.defineProperty(r,"readable",{get:()=>a.pipeThrough(l).pipeThrough(f).pipeThrough(u)})}}class Pe extends p{constructor(e){let t;super({transform:function n(r,s){if(t){const e=new i(t.length+r.length);e.set(t),e.set(r,t.length),r=e,t=null}r.length>e?(s.enqueue(r.slice(0,e)),n(r.slice(e),s)):t=r},flush(e){t&&t.length&&e.enqueue(t)}})}}const De=new a,Ve=new a;let Re,Be=0,Ee=!0;async function Me(e){try{const{options:t,scripts:r,config:s}=e;if(r&&r.length)try{Ee?importScripts.apply(k,r):await Ue(r)}catch(e){Ee=!1,await Ue(r)}self.initCodec&&self.initCodec(),s.CompressionStreamNative=self.CompressionStream,s.DecompressionStreamNative=self.DecompressionStream,self.Deflate&&(s.CompressionStream=new z(self.Deflate)),self.Inflate&&(s.DecompressionStream=new z(self.Inflate));const i={highWaterMark:1},o=e.readable||new y({async pull(e){const t=new u((e=>De.set(Be,e)));Ke({type:"pull",messageId:Be}),Be=(Be+1)%n.MAX_SAFE_INTEGER;const{value:r,done:s}=await t;e.enqueue(r),s&&e.close()}},i),c=e.writable||new m({async write(e){let t;const r=new u((e=>t=e));Ve.set(Be,t),Ke({type:Ae,value:e,messageId:Be}),Be=(Be+1)%n.MAX_SAFE_INTEGER,await r}},i),f=new Ie(t,s);Re=new AbortController;const{signal:a}=Re;await o.pipeThrough(f).pipeThrough(new Pe(s.chunkSize)).pipeTo(c,{signal:a,preventClose:!0,preventAbort:!0}),await c.getWriter().close();const{signature:l,inputSize:w,outputSize:h}=f;Ke({type:_e,result:{signature:l,inputSize:w,outputSize:h}})}catch(e){Ne(e)}}async function Ue(e){for(const t of e)await import(t)}function Ke(e){let{value:t}=e;if(t)if(t.length)try{t=new i(t),e.value=t.buffer,d(e,[e.value])}catch(t){d(e)}else d(e);else d(e)}function Ne(e=new s("Unknown error")){const{message:t,stack:n,code:r,name:i}=e;d({error:{message:t,stack:n,code:r,name:i}})}addEventListener("message",(({data:e})=>{const{type:t,messageId:n,value:r,done:s}=e;try{if("start"==t&&Me(e),t==Ae){const e=De.get(n);De.delete(n),e({value:new i(r),done:s})}if("ack"==t){const e=Ve.get(n);Ve.delete(n),e()}t==_e&&Re.abort()}catch(e){Ne(e)}}));const Oe=-2;function Te(t){return We(t.map((([t,n])=>new e(t).fill(n,0,t))))}function We(t){return t.reduce(((t,n)=>t.concat(e.isArray(n)?We(n):n)),[])}const je=[0,1,2,3].concat(...Te([[2,4],[2,5],[4,6],[4,7],[8,8],[8,9],[16,10],[16,11],[32,12],[32,13],[64,14],[64,15],[2,0],[1,16],[1,17],[2,18],[2,19],[4,20],[4,21],[8,22],[8,23],[16,24],[16,25],[32,26],[32,27],[64,28],[64,29]]));function He(){const e=this;function t(e,t){let n=0;do{n|=1&e,e>>>=1,n<<=1}while(--t>0);return n>>>1}e.ne=n=>{const s=e.re,i=e.ie.se,o=e.ie.oe;let c,f,a,l=-1;for(n.ce=0,n.fe=573,c=0;o>c;c++)0!==s[2*c]?(n.ae[++n.ce]=l=c,n.le[c]=0):s[2*c+1]=0;for(;2>n.ce;)a=n.ae[++n.ce]=2>l?++l:0,s[2*a]=1,n.le[a]=0,n.ue--,i&&(n.we-=i[2*a+1]);for(e.he=l,c=r.floor(n.ce/2);c>=1;c--)n.de(s,c);a=o;do{c=n.ae[1],n.ae[1]=n.ae[n.ce--],n.de(s,1),f=n.ae[1],n.ae[--n.fe]=c,n.ae[--n.fe]=f,s[2*a]=s[2*c]+s[2*f],n.le[a]=r.max(n.le[c],n.le[f])+1,s[2*c+1]=s[2*f+1]=a,n.ae[1]=a++,n.de(s,1)}while(n.ce>=2);n.ae[--n.fe]=n.ae[1],(t=>{const n=e.re,r=e.ie.se,s=e.ie.pe,i=e.ie.ye,o=e.ie.me;let c,f,a,l,u,w,h=0;for(l=0;15>=l;l++)t.be[l]=0;for(n[2*t.ae[t.fe]+1]=0,c=t.fe+1;573>c;c++)f=t.ae[c],l=n[2*n[2*f+1]+1]+1,l>o&&(l=o,h++),n[2*f+1]=l,f>e.he||(t.be[l]++,u=0,i>f||(u=s[f-i]),w=n[2*f],t.ue+=w*(l+u),r&&(t.we+=w*(r[2*f+1]+u)));if(0!==h){do{for(l=o-1;0===t.be[l];)l--;t.be[l]--,t.be[l+1]+=2,t.be[o]--,h-=2}while(h>0);for(l=o;0!==l;l--)for(f=t.be[l];0!==f;)a=t.ae[--c],a>e.he||(n[2*a+1]!=l&&(t.ue+=(l-n[2*a+1])*n[2*a],n[2*a+1]=l),f--)}})(n),((e,n,r)=>{const s=[];let i,o,c,f=0;for(i=1;15>=i;i++)s[i]=f=f+r[i-1]<<1;for(o=0;n>=o;o++)c=e[2*o+1],0!==c&&(e[2*o]=t(s[c]++,c))})(s,e.he,n.be)}}function Le(e,t,n,r,s){const i=this;i.se=e,i.pe=t,i.ye=n,i.oe=r,i.me=s}He.ge=[0,1,2,3,4,5,6,7].concat(...Te([[2,8],[2,9],[2,10],[2,11],[4,12],[4,13],[4,14],[4,15],[8,16],[8,17],[8,18],[8,19],[16,20],[16,21],[16,22],[16,23],[32,24],[32,25],[32,26],[31,27],[1,28]])),He.ke=[0,1,2,3,4,5,6,7,8,10,12,14,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,0],He.ve=[0,1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,3072,4096,6144,8192,12288,16384,24576],He.Se=e=>256>e?je[e]:je[256+(e>>>7)],He.ze=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0],He.Ce=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13],He.xe=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7],He.Ae=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];const Fe=Te([[144,8],[112,9],[24,7],[8,8]]);Le._e=We([12,140,76,204,44,172,108,236,28,156,92,220,60,188,124,252,2,130,66,194,34,162,98,226,18,146,82,210,50,178,114,242,10,138,74,202,42,170,106,234,26,154,90,218,58,186,122,250,6,134,70,198,38,166,102,230,22,150,86,214,54,182,118,246,14,142,78,206,46,174,110,238,30,158,94,222,62,190,126,254,1,129,65,193,33,161,97,225,17,145,81,209,49,177,113,241,9,137,73,201,41,169,105,233,25,153,89,217,57,185,121,249,5,133,69,197,37,165,101,229,21,149,85,213,53,181,117,245,13,141,77,205,45,173,109,237,29,157,93,221,61,189,125,253,19,275,147,403,83,339,211,467,51,307,179,435,115,371,243,499,11,267,139,395,75,331,203,459,43,299,171,427,107,363,235,491,27,283,155,411,91,347,219,475,59,315,187,443,123,379,251,507,7,263,135,391,71,327,199,455,39,295,167,423,103,359,231,487,23,279,151,407,87,343,215,471,55,311,183,439,119,375,247,503,15,271,143,399,79,335,207,463,47,303,175,431,111,367,239,495,31,287,159,415,95,351,223,479,63,319,191,447,127,383,255,511,0,64,32,96,16,80,48,112,8,72,40,104,24,88,56,120,4,68,36,100,20,84,52,116,3,131,67,195,35,163,99,227].map(((e,t)=>[e,Fe[t]])));const qe=Te([[30,5]]);function Ge(e,t,n,r,s){const i=this;i.Ie=e,i.Pe=t,i.De=n,i.Ve=r,i.Re=s}Le.Be=We([0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23].map(((e,t)=>[e,qe[t]]))),Le.Ee=new Le(Le._e,He.ze,257,286,15),Le.Me=new Le(Le.Be,He.Ce,0,30,15),Le.Ue=new Le(null,He.xe,0,19,7);const Je=[new Ge(0,0,0,0,0),new Ge(4,4,8,4,1),new Ge(4,5,16,8,1),new Ge(4,6,32,32,1),new Ge(4,4,16,16,2),new Ge(8,16,32,32,2),new Ge(8,16,128,128,2),new Ge(8,32,128,256,2),new Ge(32,128,258,1024,2),new Ge(32,258,258,4096,2)],Qe=["need dictionary","stream end","","","stream error","data error","","buffer error","",""],Xe=113,Ye=666,Ze=262;function $e(e,t,n,r){const s=e[2*t],i=e[2*n];return i>s||s==i&&r[t]<=r[n]}function et(){const e=this;let t,n,s,c,f,a,l,u,w,h,d,p,y,m,b,g,k,v,S,z,C,x,A,_,I,P,D,V,R,B,E,M,U;const K=new He,N=new He,O=new He;let T,W,j,H,L,F;function q(){let t;for(t=0;286>t;t++)E[2*t]=0;for(t=0;30>t;t++)M[2*t]=0;for(t=0;19>t;t++)U[2*t]=0;E[512]=1,e.ue=e.we=0,W=j=0}function G(e,t){let n,r=-1,s=e[1],i=0,o=7,c=4;0===s&&(o=138,c=3),e[2*(t+1)+1]=65535;for(let f=0;t>=f;f++)n=s,s=e[2*(f+1)+1],++i<o&&n==s||(c>i?U[2*n]+=i:0!==n?(n!=r&&U[2*n]++,U[32]++):i>10?U[36]++:U[34]++,i=0,r=n,0===s?(o=138,c=3):n==s?(o=6,c=3):(o=7,c=4))}function J(t){e.Ke[e.pending++]=t}function Q(e){J(255&e),J(e>>>8&255)}function X(e,t){let n;const r=t;F>16-r?(n=e,L|=n<<F&65535,Q(L),L=n>>>16-F,F+=r-16):(L|=e<<F&65535,F+=r)}function Y(e,t){const n=2*e;X(65535&t[n],65535&t[n+1])}function Z(e,t){let n,r,s=-1,i=e[1],o=0,c=7,f=4;for(0===i&&(c=138,f=3),n=0;t>=n;n++)if(r=i,i=e[2*(n+1)+1],++o>=c||r!=i){if(f>o)do{Y(r,U)}while(0!=--o);else 0!==r?(r!=s&&(Y(r,U),o--),Y(16,U),X(o-3,2)):o>10?(Y(18,U),X(o-11,7)):(Y(17,U),X(o-3,3));o=0,s=r,0===i?(c=138,f=3):r==i?(c=6,f=3):(c=7,f=4)}}function $(){16==F?(Q(L),L=0,F=0):8>F||(J(255&L),L>>>=8,F-=8)}function ee(t,n){let s,i,o;if(e.Ne[W]=t,e.Oe[W]=255&n,W++,0===t?E[2*n]++:(j++,t--,E[2*(He.ge[n]+256+1)]++,M[2*He.Se(t)]++),!(8191&W)&&D>2){for(s=8*W,i=C-k,o=0;30>o;o++)s+=M[2*o]*(5+He.Ce[o]);if(s>>>=3,j<r.floor(W/2)&&s<r.floor(i/2))return!0}return W==T-1}function te(t,n){let r,s,i,o,c=0;if(0!==W)do{r=e.Ne[c],s=e.Oe[c],c++,0===r?Y(s,t):(i=He.ge[s],Y(i+256+1,t),o=He.ze[i],0!==o&&(s-=He.ke[i],X(s,o)),r--,i=He.Se(r),Y(i,n),o=He.Ce[i],0!==o&&(r-=He.ve[i],X(r,o)))}while(W>c);Y(256,t),H=t[513]}function ne(){F>8?Q(L):F>0&&J(255&L),L=0,F=0}function re(t,n,r){X(0+(r?1:0),3),((t,n)=>{ne(),H=8,Q(n),Q(~n),e.Ke.set(u.subarray(t,t+n),e.pending),e.pending+=n})(t,n)}function se(n){((t,n,r)=>{let s,i,o=0;D>0?(K.ne(e),N.ne(e),o=(()=>{let t;for(G(E,K.he),G(M,N.he),O.ne(e),t=18;t>=3&&0===U[2*He.Ae[t]+1];t--);return e.ue+=14+3*(t+1),t})(),s=e.ue+3+7>>>3,i=e.we+3+7>>>3,i>s||(s=i)):s=i=n+5,n+4>s||-1==t?i==s?(X(2+(r?1:0),3),te(Le._e,Le.Be)):(X(4+(r?1:0),3),((e,t,n)=>{let r;for(X(e-257,5),X(t-1,5),X(n-4,4),r=0;n>r;r++)X(U[2*He.Ae[r]+1],3);Z(E,e-1),Z(M,t-1)})(K.he+1,N.he+1,o+1),te(E,M)):re(t,n,r),q(),r&&ne()})(0>k?-1:k,C-k,n),k=C,t.Te()}function ie(){let e,n,r,s;do{if(s=w-A-C,0===s&&0===C&&0===A)s=f;else if(-1==s)s--;else if(C>=f+f-Ze){u.set(u.subarray(f,f+f),0),x-=f,C-=f,k-=f,e=y,r=e;do{n=65535&d[--r],d[r]=f>n?0:n-f}while(0!=--e);e=f,r=e;do{n=65535&h[--r],h[r]=f>n?0:n-f}while(0!=--e);s+=f}if(0===t.We)return;e=t.je(u,C+A,s),A+=e,3>A||(p=255&u[C],p=(p<<g^255&u[C+1])&b)}while(Ze>A&&0!==t.We)}function oe(e){let t,n,r=I,s=C,i=_;const o=C>f-Ze?C-(f-Ze):0;let c=B;const a=l,w=C+258;let d=u[s+i-1],p=u[s+i];R>_||(r>>=2),c>A&&(c=A);do{if(t=e,u[t+i]==p&&u[t+i-1]==d&&u[t]==u[s]&&u[++t]==u[s+1]){s+=2,t++;do{}while(u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&w>s);if(n=258-(w-s),s=w-258,n>i){if(x=e,i=n,n>=c)break;d=u[s+i-1],p=u[s+i]}}}while((e=65535&h[e&a])>o&&0!=--r);return i>A?A:i}e.le=[],e.be=[],e.ae=[],E=[],M=[],U=[],e.de=(t,n)=>{const r=e.ae,s=r[n];let i=n<<1;for(;i<=e.ce&&(i<e.ce&&$e(t,r[i+1],r[i],e.le)&&i++,!$e(t,s,r[i],e.le));)r[n]=r[i],n=i,i<<=1;r[n]=s},e.He=(t,S,x,W,j,G)=>(W||(W=8),j||(j=8),G||(G=0),t.Le=null,-1==S&&(S=6),1>j||j>9||8!=W||9>x||x>15||0>S||S>9||0>G||G>2?Oe:(t.Fe=e,a=x,f=1<<a,l=f-1,m=j+7,y=1<<m,b=y-1,g=r.floor((m+3-1)/3),u=new i(2*f),h=[],d=[],T=1<<j+6,e.Ke=new i(4*T),s=4*T,e.Ne=new o(T),e.Oe=new i(T),D=S,V=G,(t=>(t.qe=t.Ge=0,t.Le=null,e.pending=0,e.Je=0,n=Xe,c=0,K.re=E,K.ie=Le.Ee,N.re=M,N.ie=Le.Me,O.re=U,O.ie=Le.Ue,L=0,F=0,H=8,q(),(()=>{w=2*f,d[y-1]=0;for(let e=0;y-1>e;e++)d[e]=0;P=Je[D].Pe,R=Je[D].Ie,B=Je[D].De,I=Je[D].Ve,C=0,k=0,A=0,v=_=2,z=0,p=0})(),0))(t))),e.Qe=()=>42!=n&&n!=Xe&&n!=Ye?Oe:(e.Oe=null,e.Ne=null,e.Ke=null,d=null,h=null,u=null,e.Fe=null,n==Xe?-3:0),e.Xe=(e,t,n)=>{let r=0;return-1==t&&(t=6),0>t||t>9||0>n||n>2?Oe:(Je[D].Re!=Je[t].Re&&0!==e.qe&&(r=e.Ye(1)),D!=t&&(D=t,P=Je[D].Pe,R=Je[D].Ie,B=Je[D].De,I=Je[D].Ve),V=n,r)},e.Ze=(e,t,r)=>{let s,i=r,o=0;if(!t||42!=n)return Oe;if(3>i)return 0;for(i>f-Ze&&(i=f-Ze,o=r-i),u.set(t.subarray(o,o+i),0),C=i,k=i,p=255&u[0],p=(p<<g^255&u[1])&b,s=0;i-3>=s;s++)p=(p<<g^255&u[s+2])&b,h[s&l]=d[p],d[p]=s;return 0},e.Ye=(r,i)=>{let o,w,m,I,R;if(i>4||0>i)return Oe;if(!r.$e||!r.et&&0!==r.We||n==Ye&&4!=i)return r.Le=Qe[4],Oe;if(0===r.tt)return r.Le=Qe[7],-5;var B;if(t=r,I=c,c=i,42==n&&(w=8+(a-8<<4)<<8,m=(D-1&255)>>1,m>3&&(m=3),w|=m<<6,0!==C&&(w|=32),w+=31-w%31,n=Xe,J((B=w)>>8&255),J(255&B)),0!==e.pending){if(t.Te(),0===t.tt)return c=-1,0}else if(0===t.We&&I>=i&&4!=i)return t.Le=Qe[7],-5;if(n==Ye&&0!==t.We)return r.Le=Qe[7],-5;if(0!==t.We||0!==A||0!=i&&n!=Ye){switch(R=-1,Je[D].Re){case 0:R=(e=>{let n,r=65535;for(r>s-5&&(r=s-5);;){if(1>=A){if(ie(),0===A&&0==e)return 0;if(0===A)break}if(C+=A,A=0,n=k+r,(0===C||C>=n)&&(A=C-n,C=n,se(!1),0===t.tt))return 0;if(C-k>=f-Ze&&(se(!1),0===t.tt))return 0}return se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i);break;case 1:R=(e=>{let n,r=0;for(;;){if(Ze>A){if(ie(),Ze>A&&0==e)return 0;if(0===A)break}if(3>A||(p=(p<<g^255&u[C+2])&b,r=65535&d[p],h[C&l]=d[p],d[p]=C),0===r||(C-r&65535)>f-Ze||2!=V&&(v=oe(r)),3>v)n=ee(0,255&u[C]),A--,C++;else if(n=ee(C-x,v-3),A-=v,v>P||3>A)C+=v,v=0,p=255&u[C],p=(p<<g^255&u[C+1])&b;else{v--;do{C++,p=(p<<g^255&u[C+2])&b,r=65535&d[p],h[C&l]=d[p],d[p]=C}while(0!=--v);C++}if(n&&(se(!1),0===t.tt))return 0}return se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i);break;case 2:R=(e=>{let n,r,s=0;for(;;){if(Ze>A){if(ie(),Ze>A&&0==e)return 0;if(0===A)break}if(3>A||(p=(p<<g^255&u[C+2])&b,s=65535&d[p],h[C&l]=d[p],d[p]=C),_=v,S=x,v=2,0!==s&&P>_&&f-Ze>=(C-s&65535)&&(2!=V&&(v=oe(s)),5>=v&&(1==V||3==v&&C-x>4096)&&(v=2)),3>_||v>_)if(0!==z){if(n=ee(0,255&u[C-1]),n&&se(!1),C++,A--,0===t.tt)return 0}else z=1,C++,A--;else{r=C+A-3,n=ee(C-1-S,_-3),A-=_-1,_-=2;do{++C>r||(p=(p<<g^255&u[C+2])&b,s=65535&d[p],h[C&l]=d[p],d[p]=C)}while(0!=--_);if(z=0,v=2,C++,n&&(se(!1),0===t.tt))return 0}}return 0!==z&&(n=ee(0,255&u[C-1]),z=0),se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i)}if(2!=R&&3!=R||(n=Ye),0==R||2==R)return 0===t.tt&&(c=-1),0;if(1==R){if(1==i)X(2,3),Y(256,Le._e),$(),9>1+H+10-F&&(X(2,3),Y(256,Le._e),$()),H=7;else if(re(0,0,!1),3==i)for(o=0;y>o;o++)d[o]=0;if(t.Te(),0===t.tt)return c=-1,0}}return 4!=i?0:1}}function tt(){const e=this;e.nt=0,e.rt=0,e.We=0,e.qe=0,e.tt=0,e.Ge=0}function nt(e){const t=new tt,n=(o=e&&e.chunkSize?e.chunkSize:65536)+5*(r.floor(o/16383)+1);var o;const c=new i(n);let f=e?e.level:-1;void 0===f&&(f=-1),t.He(f),t.$e=c,this.append=(e,r)=>{let o,f,a=0,l=0,u=0;const w=[];if(e.length){t.nt=0,t.et=e,t.We=e.length;do{if(t.rt=0,t.tt=n,o=t.Ye(0),0!=o)throw new s("deflating: "+t.Le);t.rt&&(t.rt==n?w.push(new i(c)):w.push(c.subarray(0,t.rt))),u+=t.rt,r&&t.nt>0&&t.nt!=a&&(r(t.nt),a=t.nt)}while(t.We>0||0===t.tt);return w.length>1?(f=new i(u),w.forEach((e=>{f.set(e,l),l+=e.length}))):f=w[0]?new i(w[0]):new i,f}},this.flush=()=>{let e,r,o=0,f=0;const a=[];do{if(t.rt=0,t.tt=n,e=t.Ye(4),1!=e&&0!=e)throw new s("deflating: "+t.Le);n-t.tt>0&&a.push(c.slice(0,t.rt)),f+=t.rt}while(t.We>0||0===t.tt);return t.Qe(),r=new i(f),a.forEach((e=>{r.set(e,o),o+=e.length})),r}}tt.prototype={He(e,t){const n=this;return n.Fe=new et,t||(t=15),n.Fe.He(n,e,t)},Ye(e){const t=this;return t.Fe?t.Fe.Ye(t,e):Oe},Qe(){const e=this;if(!e.Fe)return Oe;const t=e.Fe.Qe();return e.Fe=null,t},Xe(e,t){const n=this;return n.Fe?n.Fe.Xe(n,e,t):Oe},Ze(e,t){const n=this;return n.Fe?n.Fe.Ze(n,e,t):Oe},je(e,t,n){const r=this;let s=r.We;return s>n&&(s=n),0===s?0:(r.We-=s,e.set(r.et.subarray(r.nt,r.nt+s),t),r.nt+=s,r.qe+=s,s)},Te(){const e=this;let t=e.Fe.pending;t>e.tt&&(t=e.tt),0!==t&&(e.$e.set(e.Fe.Ke.subarray(e.Fe.Je,e.Fe.Je+t),e.rt),e.rt+=t,e.Fe.Je+=t,e.Ge+=t,e.tt-=t,e.Fe.pending-=t,0===e.Fe.pending&&(e.Fe.Je=0))}};const rt=-2,st=-3,it=-5,ot=[0,1,3,7,15,31,63,127,255,511,1023,2047,4095,8191,16383,32767,65535],ct=[96,7,256,0,8,80,0,8,16,84,8,115,82,7,31,0,8,112,0,8,48,0,9,192,80,7,10,0,8,96,0,8,32,0,9,160,0,8,0,0,8,128,0,8,64,0,9,224,80,7,6,0,8,88,0,8,24,0,9,144,83,7,59,0,8,120,0,8,56,0,9,208,81,7,17,0,8,104,0,8,40,0,9,176,0,8,8,0,8,136,0,8,72,0,9,240,80,7,4,0,8,84,0,8,20,85,8,227,83,7,43,0,8,116,0,8,52,0,9,200,81,7,13,0,8,100,0,8,36,0,9,168,0,8,4,0,8,132,0,8,68,0,9,232,80,7,8,0,8,92,0,8,28,0,9,152,84,7,83,0,8,124,0,8,60,0,9,216,82,7,23,0,8,108,0,8,44,0,9,184,0,8,12,0,8,140,0,8,76,0,9,248,80,7,3,0,8,82,0,8,18,85,8,163,83,7,35,0,8,114,0,8,50,0,9,196,81,7,11,0,8,98,0,8,34,0,9,164,0,8,2,0,8,130,0,8,66,0,9,228,80,7,7,0,8,90,0,8,26,0,9,148,84,7,67,0,8,122,0,8,58,0,9,212,82,7,19,0,8,106,0,8,42,0,9,180,0,8,10,0,8,138,0,8,74,0,9,244,80,7,5,0,8,86,0,8,22,192,8,0,83,7,51,0,8,118,0,8,54,0,9,204,81,7,15,0,8,102,0,8,38,0,9,172,0,8,6,0,8,134,0,8,70,0,9,236,80,7,9,0,8,94,0,8,30,0,9,156,84,7,99,0,8,126,0,8,62,0,9,220,82,7,27,0,8,110,0,8,46,0,9,188,0,8,14,0,8,142,0,8,78,0,9,252,96,7,256,0,8,81,0,8,17,85,8,131,82,7,31,0,8,113,0,8,49,0,9,194,80,7,10,0,8,97,0,8,33,0,9,162,0,8,1,0,8,129,0,8,65,0,9,226,80,7,6,0,8,89,0,8,25,0,9,146,83,7,59,0,8,121,0,8,57,0,9,210,81,7,17,0,8,105,0,8,41,0,9,178,0,8,9,0,8,137,0,8,73,0,9,242,80,7,4,0,8,85,0,8,21,80,8,258,83,7,43,0,8,117,0,8,53,0,9,202,81,7,13,0,8,101,0,8,37,0,9,170,0,8,5,0,8,133,0,8,69,0,9,234,80,7,8,0,8,93,0,8,29,0,9,154,84,7,83,0,8,125,0,8,61,0,9,218,82,7,23,0,8,109,0,8,45,0,9,186,0,8,13,0,8,141,0,8,77,0,9,250,80,7,3,0,8,83,0,8,19,85,8,195,83,7,35,0,8,115,0,8,51,0,9,198,81,7,11,0,8,99,0,8,35,0,9,166,0,8,3,0,8,131,0,8,67,0,9,230,80,7,7,0,8,91,0,8,27,0,9,150,84,7,67,0,8,123,0,8,59,0,9,214,82,7,19,0,8,107,0,8,43,0,9,182,0,8,11,0,8,139,0,8,75,0,9,246,80,7,5,0,8,87,0,8,23,192,8,0,83,7,51,0,8,119,0,8,55,0,9,206,81,7,15,0,8,103,0,8,39,0,9,174,0,8,7,0,8,135,0,8,71,0,9,238,80,7,9,0,8,95,0,8,31,0,9,158,84,7,99,0,8,127,0,8,63,0,9,222,82,7,27,0,8,111,0,8,47,0,9,190,0,8,15,0,8,143,0,8,79,0,9,254,96,7,256,0,8,80,0,8,16,84,8,115,82,7,31,0,8,112,0,8,48,0,9,193,80,7,10,0,8,96,0,8,32,0,9,161,0,8,0,0,8,128,0,8,64,0,9,225,80,7,6,0,8,88,0,8,24,0,9,145,83,7,59,0,8,120,0,8,56,0,9,209,81,7,17,0,8,104,0,8,40,0,9,177,0,8,8,0,8,136,0,8,72,0,9,241,80,7,4,0,8,84,0,8,20,85,8,227,83,7,43,0,8,116,0,8,52,0,9,201,81,7,13,0,8,100,0,8,36,0,9,169,0,8,4,0,8,132,0,8,68,0,9,233,80,7,8,0,8,92,0,8,28,0,9,153,84,7,83,0,8,124,0,8,60,0,9,217,82,7,23,0,8,108,0,8,44,0,9,185,0,8,12,0,8,140,0,8,76,0,9,249,80,7,3,0,8,82,0,8,18,85,8,163,83,7,35,0,8,114,0,8,50,0,9,197,81,7,11,0,8,98,0,8,34,0,9,165,0,8,2,0,8,130,0,8,66,0,9,229,80,7,7,0,8,90,0,8,26,0,9,149,84,7,67,0,8,122,0,8,58,0,9,213,82,7,19,0,8,106,0,8,42,0,9,181,0,8,10,0,8,138,0,8,74,0,9,245,80,7,5,0,8,86,0,8,22,192,8,0,83,7,51,0,8,118,0,8,54,0,9,205,81,7,15,0,8,102,0,8,38,0,9,173,0,8,6,0,8,134,0,8,70,0,9,237,80,7,9,0,8,94,0,8,30,0,9,157,84,7,99,0,8,126,0,8,62,0,9,221,82,7,27,0,8,110,0,8,46,0,9,189,0,8,14,0,8,142,0,8,78,0,9,253,96,7,256,0,8,81,0,8,17,85,8,131,82,7,31,0,8,113,0,8,49,0,9,195,80,7,10,0,8,97,0,8,33,0,9,163,0,8,1,0,8,129,0,8,65,0,9,227,80,7,6,0,8,89,0,8,25,0,9,147,83,7,59,0,8,121,0,8,57,0,9,211,81,7,17,0,8,105,0,8,41,0,9,179,0,8,9,0,8,137,0,8,73,0,9,243,80,7,4,0,8,85,0,8,21,80,8,258,83,7,43,0,8,117,0,8,53,0,9,203,81,7,13,0,8,101,0,8,37,0,9,171,0,8,5,0,8,133,0,8,69,0,9,235,80,7,8,0,8,93,0,8,29,0,9,155,84,7,83,0,8,125,0,8,61,0,9,219,82,7,23,0,8,109,0,8,45,0,9,187,0,8,13,0,8,141,0,8,77,0,9,251,80,7,3,0,8,83,0,8,19,85,8,195,83,7,35,0,8,115,0,8,51,0,9,199,81,7,11,0,8,99,0,8,35,0,9,167,0,8,3,0,8,131,0,8,67,0,9,231,80,7,7,0,8,91,0,8,27,0,9,151,84,7,67,0,8,123,0,8,59,0,9,215,82,7,19,0,8,107,0,8,43,0,9,183,0,8,11,0,8,139,0,8,75,0,9,247,80,7,5,0,8,87,0,8,23,192,8,0,83,7,51,0,8,119,0,8,55,0,9,207,81,7,15,0,8,103,0,8,39,0,9,175,0,8,7,0,8,135,0,8,71,0,9,239,80,7,9,0,8,95,0,8,31,0,9,159,84,7,99,0,8,127,0,8,63,0,9,223,82,7,27,0,8,111,0,8,47,0,9,191,0,8,15,0,8,143,0,8,79,0,9,255],ft=[80,5,1,87,5,257,83,5,17,91,5,4097,81,5,5,89,5,1025,85,5,65,93,5,16385,80,5,3,88,5,513,84,5,33,92,5,8193,82,5,9,90,5,2049,86,5,129,192,5,24577,80,5,2,87,5,385,83,5,25,91,5,6145,81,5,7,89,5,1537,85,5,97,93,5,24577,80,5,4,88,5,769,84,5,49,92,5,12289,82,5,13,90,5,3073,86,5,193,192,5,24577],at=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258,0,0],lt=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,112,112],ut=[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577],wt=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];function ht(){let e,t,n,r,s,i;function o(e,t,o,c,f,a,l,u,w,h,d){let p,y,m,b,g,k,v,S,z,C,x,A,_,I,P;C=0,g=o;do{n[e[t+C]]++,C++,g--}while(0!==g);if(n[0]==o)return l[0]=-1,u[0]=0,0;for(S=u[0],k=1;15>=k&&0===n[k];k++);for(v=k,k>S&&(S=k),g=15;0!==g&&0===n[g];g--);for(m=g,S>g&&(S=g),u[0]=S,I=1<<k;g>k;k++,I<<=1)if(0>(I-=n[k]))return st;if(0>(I-=n[g]))return st;for(n[g]+=I,i[1]=k=0,C=1,_=2;0!=--g;)i[_]=k+=n[C],_++,C++;g=0,C=0;do{0!==(k=e[t+C])&&(d[i[k]++]=g),C++}while(++g<o);for(o=i[m],i[0]=g=0,C=0,b=-1,A=-S,s[0]=0,x=0,P=0;m>=v;v++)for(p=n[v];0!=p--;){for(;v>A+S;){if(b++,A+=S,P=m-A,P=P>S?S:P,(y=1<<(k=v-A))>p+1&&(y-=p+1,_=v,P>k))for(;++k<P&&(y<<=1)>n[++_];)y-=n[_];if(P=1<<k,h[0]+P>1440)return st;s[b]=x=h[0],h[0]+=P,0!==b?(i[b]=g,r[0]=k,r[1]=S,k=g>>>A-S,r[2]=x-s[b-1]-k,w.set(r,3*(s[b-1]+k))):l[0]=x}for(r[1]=v-A,o>C?d[C]<c?(r[0]=256>d[C]?0:96,r[2]=d[C++]):(r[0]=a[d[C]-c]+16+64,r[2]=f[d[C++]-c]):r[0]=192,y=1<<v-A,k=g>>>A;P>k;k+=y)w.set(r,3*(x+k));for(k=1<<v-1;g&k;k>>>=1)g^=k;for(g^=k,z=(1<<A)-1;(g&z)!=i[b];)b--,A-=S,z=(1<<A)-1}return 0!==I&&1!=m?it:0}function c(o){let c;for(e||(e=[],t=[],n=new f(16),r=[],s=new f(15),i=new f(16)),t.length<o&&(t=[]),c=0;o>c;c++)t[c]=0;for(c=0;16>c;c++)n[c]=0;for(c=0;3>c;c++)r[c]=0;s.set(n.subarray(0,15),0),i.set(n.subarray(0,16),0)}this.st=(n,r,s,i,f)=>{let a;return c(19),e[0]=0,a=o(n,0,19,19,null,null,s,r,i,e,t),a==st?f.Le="oversubscribed dynamic bit lengths tree":a!=it&&0!==r[0]||(f.Le="incomplete dynamic bit lengths tree",a=st),a},this.it=(n,r,s,i,f,a,l,u,w)=>{let h;return c(288),e[0]=0,h=o(s,0,n,257,at,lt,a,i,u,e,t),0!=h||0===i[0]?(h==st?w.Le="oversubscribed literal/length tree":-4!=h&&(w.Le="incomplete literal/length tree",h=st),h):(c(288),h=o(s,n,r,0,ut,wt,l,f,u,e,t),0!=h||0===f[0]&&n>257?(h==st?w.Le="oversubscribed distance tree":h==it?(w.Le="incomplete distance tree",h=st):-4!=h&&(w.Le="empty distance tree with lengths",h=st),h):0)}}function dt(){const e=this;let t,n,r,s,i=0,o=0,c=0,f=0,a=0,l=0,u=0,w=0,h=0,d=0;function p(e,t,n,r,s,i,o,c){let f,a,l,u,w,h,d,p,y,m,b,g,k,v,S,z;d=c.nt,p=c.We,w=o.ot,h=o.ct,y=o.write,m=y<o.read?o.read-y-1:o.end-y,b=ot[e],g=ot[t];do{for(;20>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;if(f=w&b,a=n,l=r,z=3*(l+f),0!==(u=a[z]))for(;;){if(w>>=a[z+1],h-=a[z+1],16&u){for(u&=15,k=a[z+2]+(w&ot[u]),w>>=u,h-=u;15>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;for(f=w&g,a=s,l=i,z=3*(l+f),u=a[z];;){if(w>>=a[z+1],h-=a[z+1],16&u){for(u&=15;u>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;if(v=a[z+2]+(w&ot[u]),w>>=u,h-=u,m-=k,v>y){S=y-v;do{S+=o.end}while(0>S);if(u=o.end-S,k>u){if(k-=u,y-S>0&&u>y-S)do{o.lt[y++]=o.lt[S++]}while(0!=--u);else o.lt.set(o.lt.subarray(S,S+u),y),y+=u,S+=u,u=0;S=0}}else S=y-v,y-S>0&&2>y-S?(o.lt[y++]=o.lt[S++],o.lt[y++]=o.lt[S++],k-=2):(o.lt.set(o.lt.subarray(S,S+2),y),y+=2,S+=2,k-=2);if(y-S>0&&k>y-S)do{o.lt[y++]=o.lt[S++]}while(0!=--k);else o.lt.set(o.lt.subarray(S,S+k),y),y+=k,S+=k,k=0;break}if(64&u)return c.Le="invalid distance code",k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,st;f+=a[z+2],f+=w&ot[u],z=3*(l+f),u=a[z]}break}if(64&u)return 32&u?(k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,1):(c.Le="invalid literal/length code",k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,st);if(f+=a[z+2],f+=w&ot[u],z=3*(l+f),0===(u=a[z])){w>>=a[z+1],h-=a[z+1],o.lt[y++]=a[z+2],m--;break}}else w>>=a[z+1],h-=a[z+1],o.lt[y++]=a[z+2],m--}while(m>=258&&p>=10);return k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,0}e.init=(e,i,o,c,f,a)=>{t=0,u=e,w=i,r=o,h=c,s=f,d=a,n=null},e.ut=(e,y,m)=>{let b,g,k,v,S,z,C,x=0,A=0,_=0;for(_=y.nt,v=y.We,x=e.ot,A=e.ct,S=e.write,z=S<e.read?e.read-S-1:e.end-S;;)switch(t){case 0:if(z>=258&&v>=10&&(e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,m=p(u,w,r,h,s,d,e,y),_=y.nt,v=y.We,x=e.ot,A=e.ct,S=e.write,z=S<e.read?e.read-S-1:e.end-S,0!=m)){t=1==m?7:9;break}c=u,n=r,o=h,t=1;case 1:for(b=c;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}if(g=3*(o+(x&ot[b])),x>>>=n[g+1],A-=n[g+1],k=n[g],0===k){f=n[g+2],t=6;break}if(16&k){a=15&k,i=n[g+2],t=2;break}if(!(64&k)){c=k,o=g/3+n[g+2];break}if(32&k){t=7;break}return t=9,y.Le="invalid literal/length code",m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 2:for(b=a;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}i+=x&ot[b],x>>=b,A-=b,c=w,n=s,o=d,t=3;case 3:for(b=c;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}if(g=3*(o+(x&ot[b])),x>>=n[g+1],A-=n[g+1],k=n[g],16&k){a=15&k,l=n[g+2],t=4;break}if(!(64&k)){c=k,o=g/3+n[g+2];break}return t=9,y.Le="invalid distance code",m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 4:for(b=a;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}l+=x&ot[b],x>>=b,A-=b,t=5;case 5:for(C=S-l;0>C;)C+=e.end;for(;0!==i;){if(0===z&&(S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z&&(e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z)))return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);e.lt[S++]=e.lt[C++],z--,C==e.end&&(C=0),i--}t=0;break;case 6:if(0===z&&(S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z&&(e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z)))return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,e.lt[S++]=f,z--,t=0;break;case 7:if(A>7&&(A-=8,v++,_--),e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,e.read!=e.write)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);t=8;case 8:return m=1,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 9:return m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);default:return m=rt,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m)}},e.ht=()=>{}}ht.dt=(e,t,n,r)=>(e[0]=9,t[0]=5,n[0]=ct,r[0]=ft,0);const pt=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];function yt(e,t){const n=this;let r,s=0,o=0,c=0,a=0;const l=[0],u=[0],w=new dt;let h=0,d=new f(4320);const p=new ht;n.ct=0,n.ot=0,n.lt=new i(t),n.end=t,n.read=0,n.write=0,n.reset=(e,t)=>{t&&(t[0]=0),6==s&&w.ht(e),s=0,n.ct=0,n.ot=0,n.read=n.write=0},n.reset(e,null),n.wt=(e,t)=>{let r,s,i;return s=e.rt,i=n.read,r=(i>n.write?n.end:n.write)-i,r>e.tt&&(r=e.tt),0!==r&&t==it&&(t=0),e.tt-=r,e.Ge+=r,e.$e.set(n.lt.subarray(i,i+r),s),s+=r,i+=r,i==n.end&&(i=0,n.write==n.end&&(n.write=0),r=n.write-i,r>e.tt&&(r=e.tt),0!==r&&t==it&&(t=0),e.tt-=r,e.Ge+=r,e.$e.set(n.lt.subarray(i,i+r),s),s+=r,i+=r),e.rt=s,n.read=i,t},n.ut=(e,t)=>{let i,f,y,m,b,g,k,v;for(m=e.nt,b=e.We,f=n.ot,y=n.ct,g=n.write,k=g<n.read?n.read-g-1:n.end-g;;){let S,z,C,x,A,_,I,P;switch(s){case 0:for(;3>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}switch(i=7&f,h=1&i,i>>>1){case 0:f>>>=3,y-=3,i=7&y,f>>>=i,y-=i,s=1;break;case 1:S=[],z=[],C=[[]],x=[[]],ht.dt(S,z,C,x),w.init(S[0],z[0],C[0],0,x[0],0),f>>>=3,y-=3,s=6;break;case 2:f>>>=3,y-=3,s=3;break;case 3:return f>>>=3,y-=3,s=9,e.Le="invalid block type",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t)}break;case 1:for(;32>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if((~f>>>16&65535)!=(65535&f))return s=9,e.Le="invalid stored block lengths",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);o=65535&f,f=y=0,s=0!==o?2:0!==h?7:0;break;case 2:if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(0===k&&(g==n.end&&0!==n.read&&(g=0,k=g<n.read?n.read-g-1:n.end-g),0===k&&(n.write=g,t=n.wt(e,t),g=n.write,k=g<n.read?n.read-g-1:n.end-g,g==n.end&&0!==n.read&&(g=0,k=g<n.read?n.read-g-1:n.end-g),0===k)))return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(t=0,i=o,i>b&&(i=b),i>k&&(i=k),n.lt.set(e.je(m,i),g),m+=i,b-=i,g+=i,k-=i,0!=(o-=i))break;s=0!==h?7:0;break;case 3:for(;14>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(c=i=16383&f,(31&i)>29||(i>>5&31)>29)return s=9,e.Le="too many length or distance symbols",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(i=258+(31&i)+(i>>5&31),!r||r.length<i)r=[];else for(v=0;i>v;v++)r[v]=0;f>>>=14,y-=14,a=0,s=4;case 4:for(;4+(c>>>10)>a;){for(;3>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}r[pt[a++]]=7&f,f>>>=3,y-=3}for(;19>a;)r[pt[a++]]=0;if(l[0]=7,i=p.st(r,l,u,d,e),0!=i)return(t=i)==st&&(r=null,s=9),n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);a=0,s=5;case 5:for(;i=c,258+(31&i)+(i>>5&31)>a;){let o,w;for(i=l[0];i>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(i=d[3*(u[0]+(f&ot[i]))+1],w=d[3*(u[0]+(f&ot[i]))+2],16>w)f>>>=i,y-=i,r[a++]=w;else{for(v=18==w?7:w-14,o=18==w?11:3;i+v>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(f>>>=i,y-=i,o+=f&ot[v],f>>>=v,y-=v,v=a,i=c,v+o>258+(31&i)+(i>>5&31)||16==w&&1>v)return r=null,s=9,e.Le="invalid bit length repeat",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);w=16==w?r[v-1]:0;do{r[v++]=w}while(0!=--o);a=v}}if(u[0]=-1,A=[],_=[],I=[],P=[],A[0]=9,_[0]=6,i=c,i=p.it(257+(31&i),1+(i>>5&31),r,A,_,I,P,d,e),0!=i)return i==st&&(r=null,s=9),t=i,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);w.init(A[0],_[0],d,I[0],d,P[0]),s=6;case 6:if(n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,1!=(t=w.ut(n,e,t)))return n.wt(e,t);if(t=0,w.ht(e),m=e.nt,b=e.We,f=n.ot,y=n.ct,g=n.write,k=g<n.read?n.read-g-1:n.end-g,0===h){s=0;break}s=7;case 7:if(n.write=g,t=n.wt(e,t),g=n.write,k=g<n.read?n.read-g-1:n.end-g,n.read!=n.write)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);s=8;case 8:return t=1,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);case 9:return t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);default:return t=rt,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t)}}},n.ht=e=>{n.reset(e,null),n.lt=null,d=null},n.yt=(e,t,r)=>{n.lt.set(e.subarray(t,t+r),0),n.read=n.write=r},n.bt=()=>1==s?1:0}const mt=13,bt=[0,0,255,255];function gt(){const e=this;function t(e){return e&&e.gt?(e.qe=e.Ge=0,e.Le=null,e.gt.mode=7,e.gt.kt.reset(e,null),0):rt}e.mode=0,e.method=0,e.vt=[0],e.St=0,e.marker=0,e.zt=0,e.Ct=t=>(e.kt&&e.kt.ht(t),e.kt=null,0),e.xt=(n,r)=>(n.Le=null,e.kt=null,8>r||r>15?(e.Ct(n),rt):(e.zt=r,n.gt.kt=new yt(n,1<<r),t(n),0)),e.At=(e,t)=>{let n,r;if(!e||!e.gt||!e.et)return rt;const s=e.gt;for(t=4==t?it:0,n=it;;)switch(s.mode){case 0:if(0===e.We)return n;if(n=t,e.We--,e.qe++,8!=(15&(s.method=e.ft(e.nt++)))){s.mode=mt,e.Le="unknown compression method",s.marker=5;break}if(8+(s.method>>4)>s.zt){s.mode=mt,e.Le="invalid win size",s.marker=5;break}s.mode=1;case 1:if(0===e.We)return n;if(n=t,e.We--,e.qe++,r=255&e.ft(e.nt++),((s.method<<8)+r)%31!=0){s.mode=mt,e.Le="incorrect header check",s.marker=5;break}if(!(32&r)){s.mode=7;break}s.mode=2;case 2:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St=(255&e.ft(e.nt++))<<24&4278190080,s.mode=3;case 3:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St+=(255&e.ft(e.nt++))<<16&16711680,s.mode=4;case 4:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St+=(255&e.ft(e.nt++))<<8&65280,s.mode=5;case 5:return 0===e.We?n:(n=t,e.We--,e.qe++,s.St+=255&e.ft(e.nt++),s.mode=6,2);case 6:return s.mode=mt,e.Le="need dictionary",s.marker=0,rt;case 7:if(n=s.kt.ut(e,n),n==st){s.mode=mt,s.marker=0;break}if(0==n&&(n=t),1!=n)return n;n=t,s.kt.reset(e,s.vt),s.mode=12;case 12:return e.We=0,1;case mt:return st;default:return rt}},e._t=(e,t,n)=>{let r=0,s=n;if(!e||!e.gt||6!=e.gt.mode)return rt;const i=e.gt;return s<1<<i.zt||(s=(1<<i.zt)-1,r=n-s),i.kt.yt(t,r,s),i.mode=7,0},e.It=e=>{let n,r,s,i,o;if(!e||!e.gt)return rt;const c=e.gt;if(c.mode!=mt&&(c.mode=mt,c.marker=0),0===(n=e.We))return it;for(r=e.nt,s=c.marker;0!==n&&4>s;)e.ft(r)==bt[s]?s++:s=0!==e.ft(r)?0:4-s,r++,n--;return e.qe+=r-e.nt,e.nt=r,e.We=n,c.marker=s,4!=s?st:(i=e.qe,o=e.Ge,t(e),e.qe=i,e.Ge=o,c.mode=7,0)},e.Pt=e=>e&&e.gt&&e.gt.kt?e.gt.kt.bt():rt}function kt(){}function vt(e){const t=new kt,n=e&&e.chunkSize?r.floor(2*e.chunkSize):131072,o=new i(n);let c=!1;t.xt(),t.$e=o,this.append=(e,r)=>{const f=[];let a,l,u=0,w=0,h=0;if(0!==e.length){t.nt=0,t.et=e,t.We=e.length;do{if(t.rt=0,t.tt=n,0!==t.We||c||(t.nt=0,c=!0),a=t.At(0),c&&a===it){if(0!==t.We)throw new s("inflating: bad input")}else if(0!==a&&1!==a)throw new s("inflating: "+t.Le);if((c||1===a)&&t.We===e.length)throw new s("inflating: bad input");t.rt&&(t.rt===n?f.push(new i(o)):f.push(o.subarray(0,t.rt))),h+=t.rt,r&&t.nt>0&&t.nt!=u&&(r(t.nt),u=t.nt)}while(t.We>0||0===t.tt);return f.length>1?(l=new i(h),f.forEach((e=>{l.set(e,w),w+=e.length}))):l=f[0]?new i(f[0]):new i,l}},this.flush=()=>{t.Ct()}}kt.prototype={xt(e){const t=this;return t.gt=new gt,e||(e=15),t.gt.xt(t,e)},At(e){const t=this;return t.gt?t.gt.At(t,e):rt},Ct(){const e=this;if(!e.gt)return rt;const t=e.gt.Ct(e);return e.gt=null,t},It(){const e=this;return e.gt?e.gt.It(e):rt},_t(e,t){const n=this;return n.gt?n.gt._t(n,e,t):rt},ft(e){return this.et[e]},je(e,t){return this.et.subarray(e,e+t)}},self.initCodec=()=>{self.Deflate=nt,self.Inflate=vt};\n', r = () => t.useDataURI ? "data:text/javascript," + encodeURIComponent(n) : URL.createObjectURL(new Blob([n], { type: "text/javascript" }));
    e2({ workerScripts: { inflate: [r], deflate: [r] } });
  }

  // lib/zipjs/lib/core/io.js
  var ERR_ITERATOR_COMPLETED_TOO_SOON = "Writer iterator completed too soon";
  var HTTP_HEADER_CONTENT_TYPE = "Content-Type";
  var DEFAULT_CHUNK_SIZE = 64 * 1024;
  var PROPERTY_NAME_WRITABLE = "writable";
  var Stream = class {
    constructor() {
      this.size = 0;
    }
    init() {
      this.initialized = true;
    }
  };
  var Reader = class extends Stream {
    get readable() {
      const reader = this;
      const { chunkSize = DEFAULT_CHUNK_SIZE } = reader;
      const readable = new ReadableStream({
        start() {
          this.chunkOffset = 0;
        },
        async pull(controller) {
          const { offset = 0, size, diskNumberStart } = readable;
          const { chunkOffset } = this;
          controller.enqueue(await readUint8Array(reader, offset + chunkOffset, Math.min(chunkSize, size - chunkOffset), diskNumberStart));
          if (chunkOffset + chunkSize > size) {
            controller.close();
          } else {
            this.chunkOffset += chunkSize;
          }
        }
      });
      return readable;
    }
  };
  var BlobReader = class extends Reader {
    constructor(blob) {
      super();
      Object.assign(this, {
        blob,
        size: blob.size
      });
    }
    async readUint8Array(offset, length) {
      const reader = this;
      const offsetEnd = offset + length;
      const blob = offset || offsetEnd < reader.size ? reader.blob.slice(offset, offsetEnd) : reader.blob;
      let arrayBuffer = await blob.arrayBuffer();
      if (arrayBuffer.byteLength > length) {
        arrayBuffer = arrayBuffer.slice(offset, offsetEnd);
      }
      return new Uint8Array(arrayBuffer);
    }
  };
  var BlobWriter = class extends Stream {
    constructor(contentType) {
      super();
      const writer = this;
      const transformStream = new TransformStream();
      const headers = [];
      if (contentType) {
        headers.push([HTTP_HEADER_CONTENT_TYPE, contentType]);
      }
      Object.defineProperty(writer, PROPERTY_NAME_WRITABLE, {
        get() {
          return transformStream.writable;
        }
      });
      writer.blob = new Response(transformStream.readable, { headers }).blob();
    }
    getData() {
      return this.blob;
    }
  };
  var TextWriter = class extends BlobWriter {
    constructor(encoding) {
      super(encoding);
      Object.assign(this, {
        encoding,
        utf8: !encoding || encoding.toLowerCase() == "utf-8"
      });
    }
    async getData() {
      const {
        encoding,
        utf8
      } = this;
      const blob = await super.getData();
      if (blob.text && utf8) {
        return blob.text();
      } else {
        const reader = new FileReader();
        return new Promise((resolve, reject) => {
          Object.assign(reader, {
            onload: ({ target }) => resolve(target.result),
            onerror: () => reject(reader.error)
          });
          reader.readAsText(blob, encoding);
        });
      }
    }
  };
  var SplitDataReader = class extends Reader {
    constructor(readers) {
      super();
      this.readers = readers;
    }
    async init() {
      const reader = this;
      const { readers } = reader;
      reader.lastDiskNumber = 0;
      reader.lastDiskOffset = 0;
      await Promise.all(readers.map(async (diskReader, indexDiskReader) => {
        await diskReader.init();
        if (indexDiskReader != readers.length - 1) {
          reader.lastDiskOffset += diskReader.size;
        }
        reader.size += diskReader.size;
      }));
      super.init();
    }
    async readUint8Array(offset, length, diskNumber = 0) {
      const reader = this;
      const { readers } = this;
      let result;
      let currentDiskNumber = diskNumber;
      if (currentDiskNumber == -1) {
        currentDiskNumber = readers.length - 1;
      }
      let currentReaderOffset = offset;
      while (currentReaderOffset >= readers[currentDiskNumber].size) {
        currentReaderOffset -= readers[currentDiskNumber].size;
        currentDiskNumber++;
      }
      const currentReader = readers[currentDiskNumber];
      const currentReaderSize = currentReader.size;
      if (currentReaderOffset + length <= currentReaderSize) {
        result = await readUint8Array(currentReader, currentReaderOffset, length);
      } else {
        const chunkLength = currentReaderSize - currentReaderOffset;
        result = new Uint8Array(length);
        result.set(await readUint8Array(currentReader, currentReaderOffset, chunkLength));
        result.set(await reader.readUint8Array(offset + chunkLength, length - chunkLength, diskNumber), chunkLength);
      }
      reader.lastDiskNumber = Math.max(currentDiskNumber, reader.lastDiskNumber);
      return result;
    }
  };
  var SplitDataWriter = class extends Stream {
    constructor(writerGenerator, maxSize = 4294967295) {
      super();
      const writer = this;
      Object.assign(writer, {
        diskNumber: 0,
        diskOffset: 0,
        size: 0,
        maxSize,
        availableSize: maxSize
      });
      let diskSourceWriter, diskWritable, diskWriter;
      const writable = new WritableStream({
        async write(chunk) {
          const { availableSize } = writer;
          if (!diskWriter) {
            const { value, done } = await writerGenerator.next();
            if (done && !value) {
              throw new Error(ERR_ITERATOR_COMPLETED_TOO_SOON);
            } else {
              diskSourceWriter = value;
              diskSourceWriter.size = 0;
              if (diskSourceWriter.maxSize) {
                writer.maxSize = diskSourceWriter.maxSize;
              }
              writer.availableSize = writer.maxSize;
              await initStream(diskSourceWriter);
              diskWritable = value.writable;
              diskWriter = diskWritable.getWriter();
            }
            await this.write(chunk);
          } else if (chunk.length >= availableSize) {
            await writeChunk(chunk.slice(0, availableSize));
            await closeDisk();
            writer.diskOffset += diskSourceWriter.size;
            writer.diskNumber++;
            diskWriter = null;
            await this.write(chunk.slice(availableSize));
          } else {
            await writeChunk(chunk);
          }
        },
        async close() {
          await diskWriter.ready;
          await closeDisk();
        }
      });
      Object.defineProperty(writer, PROPERTY_NAME_WRITABLE, {
        get() {
          return writable;
        }
      });
      async function writeChunk(chunk) {
        const chunkLength = chunk.length;
        if (chunkLength) {
          await diskWriter.ready;
          await diskWriter.write(chunk);
          diskSourceWriter.size += chunkLength;
          writer.size += chunkLength;
          writer.availableSize -= chunkLength;
        }
      }
      async function closeDisk() {
        diskWritable.size = diskSourceWriter.size;
        await diskWriter.close();
      }
    }
  };
  async function initStream(stream, initSize) {
    if (stream.init && !stream.initialized) {
      await stream.init(initSize);
    } else {
      return Promise.resolve();
    }
  }
  function initReader(reader) {
    if (Array.isArray(reader)) {
      reader = new SplitDataReader(reader);
    }
    if (reader instanceof ReadableStream) {
      reader = {
        readable: reader
      };
    }
    return reader;
  }
  function initWriter(writer) {
    if (writer.writable === UNDEFINED_VALUE && typeof writer.next == FUNCTION_TYPE) {
      writer = new SplitDataWriter(writer);
    }
    if (writer instanceof WritableStream) {
      writer = {
        writable: writer
      };
    }
    const { writable } = writer;
    if (writable.size === UNDEFINED_VALUE) {
      writable.size = 0;
    }
    if (!(writer instanceof SplitDataWriter)) {
      Object.assign(writer, {
        diskNumber: 0,
        diskOffset: 0,
        availableSize: Infinity,
        maxSize: Infinity
      });
    }
    return writer;
  }
  function readUint8Array(reader, offset, size, diskNumber) {
    return reader.readUint8Array(offset, size, diskNumber);
  }

  // lib/zipjs/lib/core/util/cp437-decode.js
  var CP437 = "\0\u263A\u263B\u2665\u2666\u2663\u2660\u2022\u25D8\u25CB\u25D9\u2642\u2640\u266A\u266B\u263C\u25BA\u25C4\u2195\u203C\xB6\xA7\u25AC\u21A8\u2191\u2193\u2192\u2190\u221F\u2194\u25B2\u25BC !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\u2302\xC7\xFC\xE9\xE2\xE4\xE0\xE5\xE7\xEA\xEB\xE8\xEF\xEE\xEC\xC4\xC5\xC9\xE6\xC6\xF4\xF6\xF2\xFB\xF9\xFF\xD6\xDC\xA2\xA3\xA5\u20A7\u0192\xE1\xED\xF3\xFA\xF1\xD1\xAA\xBA\xBF\u2310\xAC\xBD\xBC\xA1\xAB\xBB\u2591\u2592\u2593\u2502\u2524\u2561\u2562\u2556\u2555\u2563\u2551\u2557\u255D\u255C\u255B\u2510\u2514\u2534\u252C\u251C\u2500\u253C\u255E\u255F\u255A\u2554\u2569\u2566\u2560\u2550\u256C\u2567\u2568\u2564\u2565\u2559\u2558\u2552\u2553\u256B\u256A\u2518\u250C\u2588\u2584\u258C\u2590\u2580\u03B1\xDF\u0393\u03C0\u03A3\u03C3\xB5\u03C4\u03A6\u0398\u03A9\u03B4\u221E\u03C6\u03B5\u2229\u2261\xB1\u2265\u2264\u2320\u2321\xF7\u2248\xB0\u2219\xB7\u221A\u207F\xB2\u25A0 ".split("");
  var VALID_CP437 = CP437.length == 256;
  function decodeCP437(stringValue) {
    if (VALID_CP437) {
      let result = "";
      for (let indexCharacter = 0; indexCharacter < stringValue.length; indexCharacter++) {
        result += CP437[stringValue[indexCharacter]];
      }
      return result;
    } else {
      return new TextDecoder().decode(stringValue);
    }
  }

  // lib/zipjs/lib/core/util/decode-text.js
  function decodeText(value, encoding) {
    if (encoding && encoding.trim().toLowerCase() == "cp437") {
      return decodeCP437(value);
    } else {
      return new TextDecoder(encoding).decode(value);
    }
  }

  // lib/zipjs/lib/core/zip-entry.js
  var PROPERTY_NAME_FILENAME = "filename";
  var PROPERTY_NAME_RAW_FILENAME = "rawFilename";
  var PROPERTY_NAME_COMMENT = "comment";
  var PROPERTY_NAME_RAW_COMMENT = "rawComment";
  var PROPERTY_NAME_UNCOMPPRESSED_SIZE = "uncompressedSize";
  var PROPERTY_NAME_COMPPRESSED_SIZE = "compressedSize";
  var PROPERTY_NAME_OFFSET = "offset";
  var PROPERTY_NAME_DISK_NUMBER_START = "diskNumberStart";
  var PROPERTY_NAME_LAST_MODIFICATION_DATE = "lastModDate";
  var PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE = "rawLastModDate";
  var PROPERTY_NAME_LAST_ACCESS_DATE = "lastAccessDate";
  var PROPERTY_NAME_RAW_LAST_ACCESS_DATE = "rawLastAccessDate";
  var PROPERTY_NAME_CREATION_DATE = "creationDate";
  var PROPERTY_NAME_RAW_CREATION_DATE = "rawCreationDate";
  var PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTE = "internalFileAttribute";
  var PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTE = "externalFileAttribute";
  var PROPERTY_NAME_MS_DOS_COMPATIBLE = "msDosCompatible";
  var PROPERTY_NAME_ZIP64 = "zip64";
  var PROPERTY_NAME_ENCRYPTED = "encrypted";
  var PROPERTY_NAME_VERSION = "version";
  var PROPERTY_NAME_VERSION_MADE_BY = "versionMadeBy";
  var PROPERTY_NAME_ZIPCRYPTO = "zipCrypto";
  var PROPERTY_NAMES = [
    PROPERTY_NAME_FILENAME,
    PROPERTY_NAME_RAW_FILENAME,
    PROPERTY_NAME_COMPPRESSED_SIZE,
    PROPERTY_NAME_UNCOMPPRESSED_SIZE,
    PROPERTY_NAME_LAST_MODIFICATION_DATE,
    PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE,
    PROPERTY_NAME_COMMENT,
    PROPERTY_NAME_RAW_COMMENT,
    PROPERTY_NAME_LAST_ACCESS_DATE,
    PROPERTY_NAME_CREATION_DATE,
    PROPERTY_NAME_OFFSET,
    PROPERTY_NAME_DISK_NUMBER_START,
    PROPERTY_NAME_DISK_NUMBER_START,
    PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTE,
    PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTE,
    PROPERTY_NAME_MS_DOS_COMPATIBLE,
    PROPERTY_NAME_ZIP64,
    PROPERTY_NAME_ENCRYPTED,
    PROPERTY_NAME_VERSION,
    PROPERTY_NAME_VERSION_MADE_BY,
    PROPERTY_NAME_ZIPCRYPTO,
    "directory",
    "bitFlag",
    "signature",
    "filenameUTF8",
    "commentUTF8",
    "compressionMethod",
    "extraField",
    "rawExtraField",
    "extraFieldZip64",
    "extraFieldUnicodePath",
    "extraFieldUnicodeComment",
    "extraFieldAES",
    "extraFieldNTFS",
    "extraFieldExtendedTimestamp"
  ];
  var Entry = class {
    constructor(data) {
      PROPERTY_NAMES.forEach((name) => this[name] = data[name]);
    }
  };

  // lib/zipjs/lib/core/zip-reader.js
  var ERR_BAD_FORMAT = "File format is not recognized";
  var ERR_EOCDR_NOT_FOUND = "End of central directory not found";
  var ERR_EOCDR_LOCATOR_ZIP64_NOT_FOUND = "End of Zip64 central directory locator not found";
  var ERR_CENTRAL_DIRECTORY_NOT_FOUND = "Central directory header not found";
  var ERR_LOCAL_FILE_HEADER_NOT_FOUND = "Local file header not found";
  var ERR_EXTRAFIELD_ZIP64_NOT_FOUND = "Zip64 extra field not found";
  var ERR_ENCRYPTED = "File contains encrypted entry";
  var ERR_UNSUPPORTED_ENCRYPTION = "Encryption method not supported";
  var ERR_UNSUPPORTED_COMPRESSION = "Compression method not supported";
  var ERR_SPLIT_ZIP_FILE = "Split zip file";
  var CHARSET_UTF8 = "utf-8";
  var CHARSET_CP437 = "cp437";
  var ZIP64_PROPERTIES = [
    [PROPERTY_NAME_UNCOMPPRESSED_SIZE, MAX_32_BITS],
    [PROPERTY_NAME_COMPPRESSED_SIZE, MAX_32_BITS],
    [PROPERTY_NAME_OFFSET, MAX_32_BITS],
    [PROPERTY_NAME_DISK_NUMBER_START, MAX_16_BITS]
  ];
  var ZIP64_EXTRACTION = {
    [MAX_16_BITS]: {
      getValue: getUint32,
      bytes: 4
    },
    [MAX_32_BITS]: {
      getValue: getBigUint64,
      bytes: 8
    }
  };
  var ZipReader = class {
    constructor(reader, options = {}) {
      Object.assign(this, {
        reader: initReader(reader),
        options,
        config: getConfiguration()
      });
    }
    async *getEntriesGenerator(options = {}) {
      const zipReader = this;
      let { reader } = zipReader;
      const { config: config3 } = zipReader;
      await initStream(reader);
      if (reader.size === UNDEFINED_VALUE || !reader.readUint8Array) {
        reader = new BlobReader(await new Response(reader.readable).blob());
        await initStream(reader);
      }
      if (reader.size < END_OF_CENTRAL_DIR_LENGTH) {
        throw new Error(ERR_BAD_FORMAT);
      }
      reader.chunkSize = getChunkSize(config3);
      const endOfDirectoryInfo = await seekSignature(reader, END_OF_CENTRAL_DIR_SIGNATURE, reader.size, END_OF_CENTRAL_DIR_LENGTH, MAX_16_BITS * 16);
      if (!endOfDirectoryInfo) {
        const signatureArray = await readUint8Array(reader, 0, 4);
        const signatureView = getDataView(signatureArray);
        if (getUint32(signatureView) == SPLIT_ZIP_FILE_SIGNATURE) {
          throw new Error(ERR_SPLIT_ZIP_FILE);
        } else {
          throw new Error(ERR_EOCDR_NOT_FOUND);
        }
      }
      const endOfDirectoryView = getDataView(endOfDirectoryInfo);
      let directoryDataLength = getUint32(endOfDirectoryView, 12);
      let directoryDataOffset = getUint32(endOfDirectoryView, 16);
      const commentOffset = endOfDirectoryInfo.offset;
      const commentLength = getUint16(endOfDirectoryView, 20);
      const appendedDataOffset = commentOffset + END_OF_CENTRAL_DIR_LENGTH + commentLength;
      let lastDiskNumber = getUint16(endOfDirectoryView, 4);
      const expectedLastDiskNumber = reader.lastDiskNumber || 0;
      let diskNumber = getUint16(endOfDirectoryView, 6);
      let filesLength = getUint16(endOfDirectoryView, 8);
      let prependedDataLength = 0;
      let startOffset = 0;
      if (directoryDataOffset == MAX_32_BITS || directoryDataLength == MAX_32_BITS || filesLength == MAX_16_BITS || diskNumber == MAX_16_BITS) {
        const endOfDirectoryLocatorArray = await readUint8Array(reader, endOfDirectoryInfo.offset - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH, ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH);
        const endOfDirectoryLocatorView = getDataView(endOfDirectoryLocatorArray);
        if (getUint32(endOfDirectoryLocatorView, 0) == ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIGNATURE) {
          directoryDataOffset = getBigUint64(endOfDirectoryLocatorView, 8);
          let endOfDirectoryArray = await readUint8Array(reader, directoryDataOffset, ZIP64_END_OF_CENTRAL_DIR_LENGTH, -1);
          let endOfDirectoryView2 = getDataView(endOfDirectoryArray);
          const expectedDirectoryDataOffset = endOfDirectoryInfo.offset - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH - ZIP64_END_OF_CENTRAL_DIR_LENGTH;
          if (getUint32(endOfDirectoryView2, 0) != ZIP64_END_OF_CENTRAL_DIR_SIGNATURE && directoryDataOffset != expectedDirectoryDataOffset) {
            const originalDirectoryDataOffset = directoryDataOffset;
            directoryDataOffset = expectedDirectoryDataOffset;
            prependedDataLength = directoryDataOffset - originalDirectoryDataOffset;
            endOfDirectoryArray = await readUint8Array(reader, directoryDataOffset, ZIP64_END_OF_CENTRAL_DIR_LENGTH, -1);
            endOfDirectoryView2 = getDataView(endOfDirectoryArray);
          }
          if (getUint32(endOfDirectoryView2, 0) != ZIP64_END_OF_CENTRAL_DIR_SIGNATURE) {
            throw new Error(ERR_EOCDR_LOCATOR_ZIP64_NOT_FOUND);
          }
          if (lastDiskNumber == MAX_16_BITS) {
            lastDiskNumber = getUint32(endOfDirectoryView2, 16);
          }
          if (diskNumber == MAX_16_BITS) {
            diskNumber = getUint32(endOfDirectoryView2, 20);
          }
          if (filesLength == MAX_16_BITS) {
            filesLength = getBigUint64(endOfDirectoryView2, 32);
          }
          if (directoryDataLength == MAX_32_BITS) {
            directoryDataLength = getBigUint64(endOfDirectoryView2, 40);
          }
          directoryDataOffset -= directoryDataLength;
        }
      }
      if (directoryDataOffset >= reader.size) {
        prependedDataLength = reader.size - directoryDataOffset - directoryDataLength - END_OF_CENTRAL_DIR_LENGTH;
        directoryDataOffset = reader.size - directoryDataLength - END_OF_CENTRAL_DIR_LENGTH;
      }
      if (expectedLastDiskNumber != lastDiskNumber) {
        throw new Error(ERR_SPLIT_ZIP_FILE);
      }
      if (directoryDataOffset < 0) {
        throw new Error(ERR_BAD_FORMAT);
      }
      let offset = 0;
      let directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
      let directoryView = getDataView(directoryArray);
      if (directoryDataLength) {
        const expectedDirectoryDataOffset = endOfDirectoryInfo.offset - directoryDataLength;
        if (getUint32(directoryView, offset) != CENTRAL_FILE_HEADER_SIGNATURE && directoryDataOffset != expectedDirectoryDataOffset) {
          const originalDirectoryDataOffset = directoryDataOffset;
          directoryDataOffset = expectedDirectoryDataOffset;
          prependedDataLength += directoryDataOffset - originalDirectoryDataOffset;
          directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
          directoryView = getDataView(directoryArray);
        }
      }
      const expectedDirectoryDataLength = endOfDirectoryInfo.offset - directoryDataOffset - (reader.lastDiskOffset || 0);
      if (directoryDataLength != expectedDirectoryDataLength && expectedDirectoryDataLength >= 0) {
        directoryDataLength = expectedDirectoryDataLength;
        directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
        directoryView = getDataView(directoryArray);
      }
      if (directoryDataOffset < 0 || directoryDataOffset >= reader.size) {
        throw new Error(ERR_BAD_FORMAT);
      }
      const filenameEncoding = getOptionValue(zipReader, options, "filenameEncoding");
      const commentEncoding = getOptionValue(zipReader, options, "commentEncoding");
      for (let indexFile = 0; indexFile < filesLength; indexFile++) {
        const fileEntry = new ZipEntry(reader, config3, zipReader.options);
        if (getUint32(directoryView, offset) != CENTRAL_FILE_HEADER_SIGNATURE) {
          throw new Error(ERR_CENTRAL_DIRECTORY_NOT_FOUND);
        }
        readCommonHeader(fileEntry, directoryView, offset + 6);
        const languageEncodingFlag = Boolean(fileEntry.bitFlag.languageEncodingFlag);
        const filenameOffset = offset + 46;
        const extraFieldOffset = filenameOffset + fileEntry.filenameLength;
        const commentOffset2 = extraFieldOffset + fileEntry.extraFieldLength;
        const versionMadeBy = getUint16(directoryView, offset + 4);
        const msDosCompatible = (versionMadeBy & 0) == 0;
        const rawFilename = directoryArray.subarray(filenameOffset, extraFieldOffset);
        const commentLength2 = getUint16(directoryView, offset + 32);
        const endOffset = commentOffset2 + commentLength2;
        const rawComment = directoryArray.subarray(commentOffset2, endOffset);
        const filenameUTF8 = languageEncodingFlag;
        const commentUTF8 = languageEncodingFlag;
        const directory = msDosCompatible && (getUint8(directoryView, offset + 38) & FILE_ATTR_MSDOS_DIR_MASK) == FILE_ATTR_MSDOS_DIR_MASK;
        const offsetFileEntry = getUint32(directoryView, offset + 42) + prependedDataLength;
        Object.assign(fileEntry, {
          versionMadeBy,
          msDosCompatible,
          compressedSize: 0,
          uncompressedSize: 0,
          commentLength: commentLength2,
          directory,
          offset: offsetFileEntry,
          diskNumberStart: getUint16(directoryView, offset + 34),
          internalFileAttribute: getUint16(directoryView, offset + 36),
          externalFileAttribute: getUint32(directoryView, offset + 38),
          rawFilename,
          filenameUTF8,
          commentUTF8,
          rawExtraField: directoryArray.subarray(extraFieldOffset, commentOffset2)
        });
        const decode = getOptionValue(zipReader, options, "decodeText") || decodeText;
        const rawFilenameEncoding = filenameUTF8 ? CHARSET_UTF8 : filenameEncoding || CHARSET_CP437;
        const rawCommentEncoding = commentUTF8 ? CHARSET_UTF8 : commentEncoding || CHARSET_CP437;
        let filename = decode(rawFilename, rawFilenameEncoding);
        if (filename === UNDEFINED_VALUE) {
          filename = decodeText(rawFilename, rawFilenameEncoding);
        }
        let comment = decode(rawComment, rawCommentEncoding);
        if (comment === UNDEFINED_VALUE) {
          comment = decodeText(rawComment, rawCommentEncoding);
        }
        Object.assign(fileEntry, {
          rawComment,
          filename,
          comment,
          directory: directory || filename.endsWith(DIRECTORY_SIGNATURE)
        });
        startOffset = Math.max(offsetFileEntry, startOffset);
        readCommonFooter(fileEntry, fileEntry, directoryView, offset + 6);
        fileEntry.zipCrypto = fileEntry.encrypted && !fileEntry.extraFieldAES;
        const entry = new Entry(fileEntry);
        entry.getData = (writer, options2) => fileEntry.getData(writer, entry, options2);
        offset = endOffset;
        const { onprogress } = options;
        if (onprogress) {
          try {
            await onprogress(indexFile + 1, filesLength, new Entry(fileEntry));
          } catch (_error) {
          }
        }
        yield entry;
      }
      const extractPrependedData = getOptionValue(zipReader, options, "extractPrependedData");
      const extractAppendedData = getOptionValue(zipReader, options, "extractAppendedData");
      if (extractPrependedData) {
        zipReader.prependedData = startOffset > 0 ? await readUint8Array(reader, 0, startOffset) : new Uint8Array();
      }
      zipReader.comment = commentLength ? await readUint8Array(reader, commentOffset + END_OF_CENTRAL_DIR_LENGTH, commentLength) : new Uint8Array();
      if (extractAppendedData) {
        zipReader.appendedData = appendedDataOffset < reader.size ? await readUint8Array(reader, appendedDataOffset, reader.size - appendedDataOffset) : new Uint8Array();
      }
      return true;
    }
    async getEntries(options = {}) {
      const entries = [];
      for await (const entry of this.getEntriesGenerator(options)) {
        entries.push(entry);
      }
      return entries;
    }
    async close() {
    }
  };
  var ZipEntry = class {
    constructor(reader, config3, options) {
      Object.assign(this, {
        reader,
        config: config3,
        options
      });
    }
    async getData(writer, fileEntry, options = {}) {
      const zipEntry = this;
      const {
        reader,
        offset,
        diskNumberStart,
        extraFieldAES,
        compressionMethod,
        config: config3,
        bitFlag,
        signature,
        rawLastModDate,
        uncompressedSize,
        compressedSize
      } = zipEntry;
      const localDirectory = fileEntry.localDirectory = {};
      const dataArray = await readUint8Array(reader, offset, 30, diskNumberStart);
      const dataView = getDataView(dataArray);
      let password = getOptionValue(zipEntry, options, "password");
      let rawPassword = getOptionValue(zipEntry, options, "rawPassword");
      const passThrough = getOptionValue(zipEntry, options, "passThrough");
      password = password && password.length && password;
      rawPassword = rawPassword && rawPassword.length && rawPassword;
      if (extraFieldAES) {
        if (extraFieldAES.originalCompressionMethod != COMPRESSION_METHOD_AES) {
          throw new Error(ERR_UNSUPPORTED_COMPRESSION);
        }
      }
      if (compressionMethod != COMPRESSION_METHOD_STORE && compressionMethod != COMPRESSION_METHOD_DEFLATE && !passThrough) {
        throw new Error(ERR_UNSUPPORTED_COMPRESSION);
      }
      if (getUint32(dataView, 0) != LOCAL_FILE_HEADER_SIGNATURE) {
        throw new Error(ERR_LOCAL_FILE_HEADER_NOT_FOUND);
      }
      readCommonHeader(localDirectory, dataView, 4);
      localDirectory.rawExtraField = localDirectory.extraFieldLength ? await readUint8Array(reader, offset + 30 + localDirectory.filenameLength, localDirectory.extraFieldLength, diskNumberStart) : new Uint8Array();
      readCommonFooter(zipEntry, localDirectory, dataView, 4, true);
      Object.assign(fileEntry, {
        lastAccessDate: localDirectory.lastAccessDate,
        creationDate: localDirectory.creationDate
      });
      const encrypted = zipEntry.encrypted && localDirectory.encrypted && !passThrough;
      const zipCrypto = encrypted && !extraFieldAES;
      if (!passThrough) {
        fileEntry.zipCrypto = zipCrypto;
      }
      if (encrypted) {
        if (!zipCrypto && extraFieldAES.strength === UNDEFINED_VALUE) {
          throw new Error(ERR_UNSUPPORTED_ENCRYPTION);
        } else if (!password && !rawPassword) {
          throw new Error(ERR_ENCRYPTED);
        }
      }
      const dataOffset = offset + 30 + localDirectory.filenameLength + localDirectory.extraFieldLength;
      const size = compressedSize;
      const readable = reader.readable;
      Object.assign(readable, {
        diskNumberStart,
        offset: dataOffset,
        size
      });
      const signal = getOptionValue(zipEntry, options, "signal");
      const checkPasswordOnly = getOptionValue(zipEntry, options, "checkPasswordOnly");
      if (checkPasswordOnly) {
        writer = new WritableStream();
      }
      writer = initWriter(writer);
      await initStream(writer, passThrough ? compressedSize : uncompressedSize);
      const { writable } = writer;
      const { onstart, onprogress, onend } = options;
      const workerOptions = {
        options: {
          codecType: CODEC_INFLATE,
          password,
          rawPassword,
          zipCrypto,
          encryptionStrength: extraFieldAES && extraFieldAES.strength,
          signed: getOptionValue(zipEntry, options, "checkSignature") && !passThrough,
          passwordVerification: zipCrypto && (bitFlag.dataDescriptor ? rawLastModDate >>> 8 & 255 : signature >>> 24 & 255),
          signature,
          compressed: compressionMethod != 0 && !passThrough,
          encrypted: zipEntry.encrypted && !passThrough,
          useWebWorkers: getOptionValue(zipEntry, options, "useWebWorkers"),
          useCompressionStream: getOptionValue(zipEntry, options, "useCompressionStream"),
          transferStreams: getOptionValue(zipEntry, options, "transferStreams"),
          checkPasswordOnly
        },
        config: config3,
        streamOptions: { signal, size, onstart, onprogress, onend }
      };
      let outputSize = 0;
      try {
        ({ outputSize } = await runWorker2({ readable, writable }, workerOptions));
      } catch (error) {
        if (!checkPasswordOnly || error.message != ERR_ABORT_CHECK_PASSWORD) {
          throw error;
        }
      } finally {
        const preventClose = getOptionValue(zipEntry, options, "preventClose");
        writable.size += outputSize;
        if (!preventClose && !writable.locked) {
          await writable.getWriter().close();
        }
      }
      return checkPasswordOnly ? UNDEFINED_VALUE : writer.getData ? writer.getData() : writable;
    }
  };
  function readCommonHeader(directory, dataView, offset) {
    const rawBitFlag = directory.rawBitFlag = getUint16(dataView, offset + 2);
    const encrypted = (rawBitFlag & BITFLAG_ENCRYPTED) == BITFLAG_ENCRYPTED;
    const rawLastModDate = getUint32(dataView, offset + 6);
    Object.assign(directory, {
      encrypted,
      version: getUint16(dataView, offset),
      bitFlag: {
        level: (rawBitFlag & BITFLAG_LEVEL) >> 1,
        dataDescriptor: (rawBitFlag & BITFLAG_DATA_DESCRIPTOR) == BITFLAG_DATA_DESCRIPTOR,
        languageEncodingFlag: (rawBitFlag & BITFLAG_LANG_ENCODING_FLAG) == BITFLAG_LANG_ENCODING_FLAG
      },
      rawLastModDate,
      lastModDate: getDate(rawLastModDate),
      filenameLength: getUint16(dataView, offset + 22),
      extraFieldLength: getUint16(dataView, offset + 24)
    });
  }
  function readCommonFooter(fileEntry, directory, dataView, offset, localDirectory) {
    const { rawExtraField } = directory;
    const extraField = directory.extraField = /* @__PURE__ */ new Map();
    const rawExtraFieldView = getDataView(new Uint8Array(rawExtraField));
    let offsetExtraField = 0;
    try {
      while (offsetExtraField < rawExtraField.length) {
        const type = getUint16(rawExtraFieldView, offsetExtraField);
        const size = getUint16(rawExtraFieldView, offsetExtraField + 2);
        extraField.set(type, {
          type,
          data: rawExtraField.slice(offsetExtraField + 4, offsetExtraField + 4 + size)
        });
        offsetExtraField += 4 + size;
      }
    } catch (_error) {
    }
    const compressionMethod = getUint16(dataView, offset + 4);
    Object.assign(directory, {
      signature: getUint32(dataView, offset + 10),
      uncompressedSize: getUint32(dataView, offset + 18),
      compressedSize: getUint32(dataView, offset + 14)
    });
    const extraFieldZip64 = extraField.get(EXTRAFIELD_TYPE_ZIP64);
    if (extraFieldZip64) {
      readExtraFieldZip64(extraFieldZip64, directory);
      directory.extraFieldZip64 = extraFieldZip64;
    }
    const extraFieldUnicodePath = extraField.get(EXTRAFIELD_TYPE_UNICODE_PATH);
    if (extraFieldUnicodePath) {
      readExtraFieldUnicode(extraFieldUnicodePath, PROPERTY_NAME_FILENAME, PROPERTY_NAME_RAW_FILENAME, directory, fileEntry);
      directory.extraFieldUnicodePath = extraFieldUnicodePath;
    }
    const extraFieldUnicodeComment = extraField.get(EXTRAFIELD_TYPE_UNICODE_COMMENT);
    if (extraFieldUnicodeComment) {
      readExtraFieldUnicode(extraFieldUnicodeComment, PROPERTY_NAME_COMMENT, PROPERTY_NAME_RAW_COMMENT, directory, fileEntry);
      directory.extraFieldUnicodeComment = extraFieldUnicodeComment;
    }
    const extraFieldAES = extraField.get(EXTRAFIELD_TYPE_AES);
    if (extraFieldAES) {
      readExtraFieldAES(extraFieldAES, directory, compressionMethod);
      directory.extraFieldAES = extraFieldAES;
    } else {
      directory.compressionMethod = compressionMethod;
    }
    const extraFieldNTFS = extraField.get(EXTRAFIELD_TYPE_NTFS);
    if (extraFieldNTFS) {
      readExtraFieldNTFS(extraFieldNTFS, directory);
      directory.extraFieldNTFS = extraFieldNTFS;
    }
    const extraFieldExtendedTimestamp = extraField.get(EXTRAFIELD_TYPE_EXTENDED_TIMESTAMP);
    if (extraFieldExtendedTimestamp) {
      readExtraFieldExtendedTimestamp(extraFieldExtendedTimestamp, directory, localDirectory);
      directory.extraFieldExtendedTimestamp = extraFieldExtendedTimestamp;
    }
    const extraFieldUSDZ = extraField.get(EXTRAFIELD_TYPE_USDZ);
    if (extraFieldUSDZ) {
      directory.extraFieldUSDZ = extraFieldUSDZ;
    }
  }
  function readExtraFieldZip64(extraFieldZip64, directory) {
    directory.zip64 = true;
    const extraFieldView = getDataView(extraFieldZip64.data);
    const missingProperties = ZIP64_PROPERTIES.filter(([propertyName, max]) => directory[propertyName] == max);
    for (let indexMissingProperty = 0, offset = 0; indexMissingProperty < missingProperties.length; indexMissingProperty++) {
      const [propertyName, max] = missingProperties[indexMissingProperty];
      if (directory[propertyName] == max) {
        const extraction = ZIP64_EXTRACTION[max];
        directory[propertyName] = extraFieldZip64[propertyName] = extraction.getValue(extraFieldView, offset);
        offset += extraction.bytes;
      } else if (extraFieldZip64[propertyName]) {
        throw new Error(ERR_EXTRAFIELD_ZIP64_NOT_FOUND);
      }
    }
  }
  function readExtraFieldUnicode(extraFieldUnicode, propertyName, rawPropertyName, directory, fileEntry) {
    const extraFieldView = getDataView(extraFieldUnicode.data);
    const crc322 = new Crc32();
    crc322.append(fileEntry[rawPropertyName]);
    const dataViewSignature = getDataView(new Uint8Array(4));
    dataViewSignature.setUint32(0, crc322.get(), true);
    const signature = getUint32(extraFieldView, 1);
    Object.assign(extraFieldUnicode, {
      version: getUint8(extraFieldView, 0),
      [propertyName]: decodeText(extraFieldUnicode.data.subarray(5)),
      valid: !fileEntry.bitFlag.languageEncodingFlag && signature == getUint32(dataViewSignature, 0)
    });
    if (extraFieldUnicode.valid) {
      directory[propertyName] = extraFieldUnicode[propertyName];
      directory[propertyName + "UTF8"] = true;
    }
  }
  function readExtraFieldAES(extraFieldAES, directory, compressionMethod) {
    const extraFieldView = getDataView(extraFieldAES.data);
    const strength = getUint8(extraFieldView, 4);
    Object.assign(extraFieldAES, {
      vendorVersion: getUint8(extraFieldView, 0),
      vendorId: getUint8(extraFieldView, 2),
      strength,
      originalCompressionMethod: compressionMethod,
      compressionMethod: getUint16(extraFieldView, 5)
    });
    directory.compressionMethod = extraFieldAES.compressionMethod;
  }
  function readExtraFieldNTFS(extraFieldNTFS, directory) {
    const extraFieldView = getDataView(extraFieldNTFS.data);
    let offsetExtraField = 4;
    let tag1Data;
    try {
      while (offsetExtraField < extraFieldNTFS.data.length && !tag1Data) {
        const tagValue = getUint16(extraFieldView, offsetExtraField);
        const attributeSize = getUint16(extraFieldView, offsetExtraField + 2);
        if (tagValue == EXTRAFIELD_TYPE_NTFS_TAG1) {
          tag1Data = extraFieldNTFS.data.slice(offsetExtraField + 4, offsetExtraField + 4 + attributeSize);
        }
        offsetExtraField += 4 + attributeSize;
      }
    } catch (_error) {
    }
    try {
      if (tag1Data && tag1Data.length == 24) {
        const tag1View = getDataView(tag1Data);
        const rawLastModDate = tag1View.getBigUint64(0, true);
        const rawLastAccessDate = tag1View.getBigUint64(8, true);
        const rawCreationDate = tag1View.getBigUint64(16, true);
        Object.assign(extraFieldNTFS, {
          rawLastModDate,
          rawLastAccessDate,
          rawCreationDate
        });
        const lastModDate = getDateNTFS(rawLastModDate);
        const lastAccessDate = getDateNTFS(rawLastAccessDate);
        const creationDate = getDateNTFS(rawCreationDate);
        const extraFieldData = { lastModDate, lastAccessDate, creationDate };
        Object.assign(extraFieldNTFS, extraFieldData);
        Object.assign(directory, extraFieldData);
      }
    } catch (_error) {
    }
  }
  function readExtraFieldExtendedTimestamp(extraFieldExtendedTimestamp, directory, localDirectory) {
    const extraFieldView = getDataView(extraFieldExtendedTimestamp.data);
    const flags = getUint8(extraFieldView, 0);
    const timeProperties = [];
    const timeRawProperties = [];
    if (localDirectory) {
      if ((flags & 1) == 1) {
        timeProperties.push(PROPERTY_NAME_LAST_MODIFICATION_DATE);
        timeRawProperties.push(PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE);
      }
      if ((flags & 2) == 2) {
        timeProperties.push(PROPERTY_NAME_LAST_ACCESS_DATE);
        timeRawProperties.push(PROPERTY_NAME_RAW_LAST_ACCESS_DATE);
      }
      if ((flags & 4) == 4) {
        timeProperties.push(PROPERTY_NAME_CREATION_DATE);
        timeRawProperties.push(PROPERTY_NAME_RAW_CREATION_DATE);
      }
    } else if (extraFieldExtendedTimestamp.data.length >= 5) {
      timeProperties.push(PROPERTY_NAME_LAST_MODIFICATION_DATE);
      timeRawProperties.push(PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE);
    }
    let offset = 1;
    timeProperties.forEach((propertyName, indexProperty) => {
      if (extraFieldExtendedTimestamp.data.length >= offset + 4) {
        const time = getUint32(extraFieldView, offset);
        directory[propertyName] = extraFieldExtendedTimestamp[propertyName] = new Date(time * 1e3);
        const rawPropertyName = timeRawProperties[indexProperty];
        extraFieldExtendedTimestamp[rawPropertyName] = time;
      }
      offset += 4;
    });
  }
  async function seekSignature(reader, signature, startOffset, minimumBytes, maximumLength) {
    const signatureArray = new Uint8Array(4);
    const signatureView = getDataView(signatureArray);
    setUint32(signatureView, 0, signature);
    const maximumBytes = minimumBytes + maximumLength;
    return await seek(minimumBytes) || await seek(Math.min(maximumBytes, startOffset));
    async function seek(length) {
      const offset = startOffset - length;
      const bytes = await readUint8Array(reader, offset, length);
      for (let indexByte = bytes.length - minimumBytes; indexByte >= 0; indexByte--) {
        if (bytes[indexByte] == signatureArray[0] && bytes[indexByte + 1] == signatureArray[1] && bytes[indexByte + 2] == signatureArray[2] && bytes[indexByte + 3] == signatureArray[3]) {
          return {
            offset: offset + indexByte,
            buffer: bytes.slice(indexByte, indexByte + minimumBytes).buffer
          };
        }
      }
    }
  }
  function getOptionValue(zipReader, options, name) {
    return options[name] === UNDEFINED_VALUE ? zipReader.options[name] : options[name];
  }
  function getDate(timeRaw) {
    const date = (timeRaw & 4294901760) >> 16, time = timeRaw & 65535;
    try {
      return new Date(1980 + ((date & 65024) >> 9), ((date & 480) >> 5) - 1, date & 31, (time & 63488) >> 11, (time & 2016) >> 5, (time & 31) * 2, 0);
    } catch (_error) {
    }
  }
  function getDateNTFS(timeRaw) {
    return new Date(Number(timeRaw / BigInt(1e4) - BigInt(116444736e5)));
  }
  function getUint8(view, offset) {
    return view.getUint8(offset);
  }
  function getUint16(view, offset) {
    return view.getUint16(offset, true);
  }
  function getUint32(view, offset) {
    return view.getUint32(offset, true);
  }
  function getBigUint64(view, offset) {
    return Number(view.getBigUint64(offset, true));
  }
  function setUint32(view, offset, value) {
    view.setUint32(offset, value, true);
  }
  function getDataView(array) {
    return new DataView(array.buffer);
  }

  // lib/zipjs/lib/core/zip-writer.js
  var EXTRAFIELD_DATA_AES = new Uint8Array([7, 0, 2, 0, 65, 69, 3, 0, 0]);

  // lib/zipjs/lib/zip-fs.js
  var import_meta = {};
  var baseURL;
  try {
    baseURL = import_meta.url;
  } catch (_error) {
  }
  configure({ baseURL });
  e(configure);

  // lib/zipjs/index.js
  configure({ Deflate: ZipDeflate, Inflate: ZipInflate });

  // src/Play.ts
  var Play = class _Play {
    constructor(ts, ms_played, master_metadata_track_name, master_metadata_album_artist_name, master_metadata_album_album_name, spotify_track_uri, reason_start, reason_end, shuffle, skipped) {
      this.ts = new Date(ts);
      this.ms_played = ms_played;
      this.master_metadata_track_name = master_metadata_track_name;
      this.master_metadata_album_artist_name = master_metadata_album_artist_name;
      this.master_metadata_album_album_name = master_metadata_album_album_name;
      this.spotify_track_uri = spotify_track_uri;
      this.reason_start = reason_start;
      this.reason_end = reason_end;
      this.shuffle = shuffle;
      this.skipped = skipped;
    }
    static fromJsonObject(item) {
      return new _Play(
        item.ts,
        item.ms_played,
        item.master_metadata_track_name,
        item.master_metadata_album_artist_name,
        item.master_metadata_album_album_name,
        item.spotify_track_uri,
        item.reason_start,
        item.reason_end,
        item.shuffle,
        item.skipped
      );
    }
  };

  // src/Album.ts
  var Album = class {
    constructor(artistName, albumName) {
      this.playCountBySongTitle = {};
      this.arbitraryTrackId = null;
      this.artistName = artistName;
      this.albumName = albumName;
      this.numPlays = 0;
    }
    setArbitraryTrackId(id) {
      this.arbitraryTrackId = id;
    }
    getArbitraryTrackId() {
      return this.arbitraryTrackId;
    }
    addPlayForTrack(trackName) {
      if (!(trackName in this.playCountBySongTitle)) {
        this.playCountBySongTitle[trackName] = 0;
      }
      this.playCountBySongTitle[trackName]++;
      this.numPlays++;
    }
    getNumPlays() {
      return this.numPlays;
    }
    getNumPlaysOfNthMostPlayedSong(n) {
      const playCounts = Object.values(this.playCountBySongTitle);
      if (n <= 0 || n > playCounts.length) {
        return 0;
      }
      const sortedCounts = playCounts.sort((a, b) => b - a);
      return sortedCounts[n - 1];
    }
    getNumDistinctSongsPlayed() {
      return Object.keys(this.playCountBySongTitle).length;
    }
  };

  // src/AlbumCollection.ts
  var AlbumCollection = class {
    constructor() {
      this.albumsByArtistAlbumString = {};
    }
    addPlay(p) {
      const artistName = p.master_metadata_album_artist_name;
      const albumName = p.master_metadata_album_album_name;
      if (artistName && albumName) {
        const standardizedAlbumName = this.standardizeAlbumTitle(albumName);
        let key = artistName + " - " + standardizedAlbumName;
        if (!(key in this.albumsByArtistAlbumString)) {
          this.albumsByArtistAlbumString[key] = new Album(artistName, standardizedAlbumName);
        }
        const album = this.albumsByArtistAlbumString[key];
        album.addPlayForTrack(p.master_metadata_track_name);
        if (!album.getArbitraryTrackId()) {
          album.setArbitraryTrackId(p.spotify_track_uri.replace(/^spotify:track:/, ""));
        }
      }
    }
    standardizeAlbumTitle(albumTitle) {
      return albumTitle;
    }
    getAlbums() {
      return Object.values(this.albumsByArtistAlbumString);
    }
  };

  // src/AlbumForDisplay.ts
  var AlbumForDisplay = class {
    constructor(albumTitle, artistTitle, imageUrl) {
      this.albumTitle = albumTitle;
      this.artistName = artistTitle;
      this.imageUrl = imageUrl;
    }
  };

  // node_modules/pako/dist/pako.esm.mjs
  var Z_FIXED$1 = 4;
  var Z_BINARY = 0;
  var Z_TEXT = 1;
  var Z_UNKNOWN$1 = 2;
  function zero$1(buf) {
    let len = buf.length;
    while (--len >= 0) {
      buf[len] = 0;
    }
  }
  var STORED_BLOCK2 = 0;
  var STATIC_TREES2 = 1;
  var DYN_TREES2 = 2;
  var MIN_MATCH$1 = 3;
  var MAX_MATCH$1 = 258;
  var LENGTH_CODES$1 = 29;
  var LITERALS$1 = 256;
  var L_CODES$1 = LITERALS$1 + 1 + LENGTH_CODES$1;
  var D_CODES$1 = 30;
  var BL_CODES$1 = 19;
  var HEAP_SIZE$1 = 2 * L_CODES$1 + 1;
  var MAX_BITS$1 = 15;
  var Buf_size2 = 16;
  var MAX_BL_BITS2 = 7;
  var END_BLOCK2 = 256;
  var REP_3_62 = 16;
  var REPZ_3_102 = 17;
  var REPZ_11_1382 = 18;
  var extra_lbits = (
    /* extra bits for each length code */
    new Uint8Array([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0])
  );
  var extra_dbits = (
    /* extra bits for each distance code */
    new Uint8Array([0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13])
  );
  var extra_blbits = (
    /* extra bits for each bit length code */
    new Uint8Array([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7])
  );
  var bl_order = new Uint8Array([16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]);
  var DIST_CODE_LEN = 512;
  var static_ltree = new Array((L_CODES$1 + 2) * 2);
  zero$1(static_ltree);
  var static_dtree = new Array(D_CODES$1 * 2);
  zero$1(static_dtree);
  var _dist_code2 = new Array(DIST_CODE_LEN);
  zero$1(_dist_code2);
  var _length_code = new Array(MAX_MATCH$1 - MIN_MATCH$1 + 1);
  zero$1(_length_code);
  var base_length = new Array(LENGTH_CODES$1);
  zero$1(base_length);
  var base_dist = new Array(D_CODES$1);
  zero$1(base_dist);
  function StaticTreeDesc(static_tree, extra_bits, extra_base, elems, max_length) {
    this.static_tree = static_tree;
    this.extra_bits = extra_bits;
    this.extra_base = extra_base;
    this.elems = elems;
    this.max_length = max_length;
    this.has_stree = static_tree && static_tree.length;
  }
  var static_l_desc;
  var static_d_desc;
  var static_bl_desc;
  function TreeDesc(dyn_tree, stat_desc) {
    this.dyn_tree = dyn_tree;
    this.max_code = 0;
    this.stat_desc = stat_desc;
  }
  var d_code = (dist) => {
    return dist < 256 ? _dist_code2[dist] : _dist_code2[256 + (dist >>> 7)];
  };
  var put_short = (s, w) => {
    s.pending_buf[s.pending++] = w & 255;
    s.pending_buf[s.pending++] = w >>> 8 & 255;
  };
  var send_bits = (s, value, length) => {
    if (s.bi_valid > Buf_size2 - length) {
      s.bi_buf |= value << s.bi_valid & 65535;
      put_short(s, s.bi_buf);
      s.bi_buf = value >> Buf_size2 - s.bi_valid;
      s.bi_valid += length - Buf_size2;
    } else {
      s.bi_buf |= value << s.bi_valid & 65535;
      s.bi_valid += length;
    }
  };
  var send_code = (s, c, tree) => {
    send_bits(
      s,
      tree[c * 2],
      tree[c * 2 + 1]
      /*.Len*/
    );
  };
  var bi_reverse = (code2, len) => {
    let res = 0;
    do {
      res |= code2 & 1;
      code2 >>>= 1;
      res <<= 1;
    } while (--len > 0);
    return res >>> 1;
  };
  var bi_flush = (s) => {
    if (s.bi_valid === 16) {
      put_short(s, s.bi_buf);
      s.bi_buf = 0;
      s.bi_valid = 0;
    } else if (s.bi_valid >= 8) {
      s.pending_buf[s.pending++] = s.bi_buf & 255;
      s.bi_buf >>= 8;
      s.bi_valid -= 8;
    }
  };
  var gen_bitlen = (s, desc) => {
    const tree = desc.dyn_tree;
    const max_code = desc.max_code;
    const stree = desc.stat_desc.static_tree;
    const has_stree = desc.stat_desc.has_stree;
    const extra = desc.stat_desc.extra_bits;
    const base = desc.stat_desc.extra_base;
    const max_length = desc.stat_desc.max_length;
    let h;
    let n, m;
    let bits;
    let xbits;
    let f;
    let overflow = 0;
    for (bits = 0; bits <= MAX_BITS$1; bits++) {
      s.bl_count[bits] = 0;
    }
    tree[s.heap[s.heap_max] * 2 + 1] = 0;
    for (h = s.heap_max + 1; h < HEAP_SIZE$1; h++) {
      n = s.heap[h];
      bits = tree[tree[n * 2 + 1] * 2 + 1] + 1;
      if (bits > max_length) {
        bits = max_length;
        overflow++;
      }
      tree[n * 2 + 1] = bits;
      if (n > max_code) {
        continue;
      }
      s.bl_count[bits]++;
      xbits = 0;
      if (n >= base) {
        xbits = extra[n - base];
      }
      f = tree[n * 2];
      s.opt_len += f * (bits + xbits);
      if (has_stree) {
        s.static_len += f * (stree[n * 2 + 1] + xbits);
      }
    }
    if (overflow === 0) {
      return;
    }
    do {
      bits = max_length - 1;
      while (s.bl_count[bits] === 0) {
        bits--;
      }
      s.bl_count[bits]--;
      s.bl_count[bits + 1] += 2;
      s.bl_count[max_length]--;
      overflow -= 2;
    } while (overflow > 0);
    for (bits = max_length; bits !== 0; bits--) {
      n = s.bl_count[bits];
      while (n !== 0) {
        m = s.heap[--h];
        if (m > max_code) {
          continue;
        }
        if (tree[m * 2 + 1] !== bits) {
          s.opt_len += (bits - tree[m * 2 + 1]) * tree[m * 2];
          tree[m * 2 + 1] = bits;
        }
        n--;
      }
    }
  };
  var gen_codes = (tree, max_code, bl_count) => {
    const next_code = new Array(MAX_BITS$1 + 1);
    let code2 = 0;
    let bits;
    let n;
    for (bits = 1; bits <= MAX_BITS$1; bits++) {
      code2 = code2 + bl_count[bits - 1] << 1;
      next_code[bits] = code2;
    }
    for (n = 0; n <= max_code; n++) {
      let len = tree[n * 2 + 1];
      if (len === 0) {
        continue;
      }
      tree[n * 2] = bi_reverse(next_code[len]++, len);
    }
  };
  var tr_static_init = () => {
    let n;
    let bits;
    let length;
    let code2;
    let dist;
    const bl_count = new Array(MAX_BITS$1 + 1);
    length = 0;
    for (code2 = 0; code2 < LENGTH_CODES$1 - 1; code2++) {
      base_length[code2] = length;
      for (n = 0; n < 1 << extra_lbits[code2]; n++) {
        _length_code[length++] = code2;
      }
    }
    _length_code[length - 1] = code2;
    dist = 0;
    for (code2 = 0; code2 < 16; code2++) {
      base_dist[code2] = dist;
      for (n = 0; n < 1 << extra_dbits[code2]; n++) {
        _dist_code2[dist++] = code2;
      }
    }
    dist >>= 7;
    for (; code2 < D_CODES$1; code2++) {
      base_dist[code2] = dist << 7;
      for (n = 0; n < 1 << extra_dbits[code2] - 7; n++) {
        _dist_code2[256 + dist++] = code2;
      }
    }
    for (bits = 0; bits <= MAX_BITS$1; bits++) {
      bl_count[bits] = 0;
    }
    n = 0;
    while (n <= 143) {
      static_ltree[n * 2 + 1] = 8;
      n++;
      bl_count[8]++;
    }
    while (n <= 255) {
      static_ltree[n * 2 + 1] = 9;
      n++;
      bl_count[9]++;
    }
    while (n <= 279) {
      static_ltree[n * 2 + 1] = 7;
      n++;
      bl_count[7]++;
    }
    while (n <= 287) {
      static_ltree[n * 2 + 1] = 8;
      n++;
      bl_count[8]++;
    }
    gen_codes(static_ltree, L_CODES$1 + 1, bl_count);
    for (n = 0; n < D_CODES$1; n++) {
      static_dtree[n * 2 + 1] = 5;
      static_dtree[n * 2] = bi_reverse(n, 5);
    }
    static_l_desc = new StaticTreeDesc(static_ltree, extra_lbits, LITERALS$1 + 1, L_CODES$1, MAX_BITS$1);
    static_d_desc = new StaticTreeDesc(static_dtree, extra_dbits, 0, D_CODES$1, MAX_BITS$1);
    static_bl_desc = new StaticTreeDesc(new Array(0), extra_blbits, 0, BL_CODES$1, MAX_BL_BITS2);
  };
  var init_block = (s) => {
    let n;
    for (n = 0; n < L_CODES$1; n++) {
      s.dyn_ltree[n * 2] = 0;
    }
    for (n = 0; n < D_CODES$1; n++) {
      s.dyn_dtree[n * 2] = 0;
    }
    for (n = 0; n < BL_CODES$1; n++) {
      s.bl_tree[n * 2] = 0;
    }
    s.dyn_ltree[END_BLOCK2 * 2] = 1;
    s.opt_len = s.static_len = 0;
    s.sym_next = s.matches = 0;
  };
  var bi_windup = (s) => {
    if (s.bi_valid > 8) {
      put_short(s, s.bi_buf);
    } else if (s.bi_valid > 0) {
      s.pending_buf[s.pending++] = s.bi_buf;
    }
    s.bi_buf = 0;
    s.bi_valid = 0;
  };
  var smaller2 = (tree, n, m, depth) => {
    const _n2 = n * 2;
    const _m2 = m * 2;
    return tree[_n2] < tree[_m2] || tree[_n2] === tree[_m2] && depth[n] <= depth[m];
  };
  var pqdownheap = (s, tree, k) => {
    const v = s.heap[k];
    let j = k << 1;
    while (j <= s.heap_len) {
      if (j < s.heap_len && smaller2(tree, s.heap[j + 1], s.heap[j], s.depth)) {
        j++;
      }
      if (smaller2(tree, v, s.heap[j], s.depth)) {
        break;
      }
      s.heap[k] = s.heap[j];
      k = j;
      j <<= 1;
    }
    s.heap[k] = v;
  };
  var compress_block = (s, ltree, dtree) => {
    let dist;
    let lc;
    let sx = 0;
    let code2;
    let extra;
    if (s.sym_next !== 0) {
      do {
        dist = s.pending_buf[s.sym_buf + sx++] & 255;
        dist += (s.pending_buf[s.sym_buf + sx++] & 255) << 8;
        lc = s.pending_buf[s.sym_buf + sx++];
        if (dist === 0) {
          send_code(s, lc, ltree);
        } else {
          code2 = _length_code[lc];
          send_code(s, code2 + LITERALS$1 + 1, ltree);
          extra = extra_lbits[code2];
          if (extra !== 0) {
            lc -= base_length[code2];
            send_bits(s, lc, extra);
          }
          dist--;
          code2 = d_code(dist);
          send_code(s, code2, dtree);
          extra = extra_dbits[code2];
          if (extra !== 0) {
            dist -= base_dist[code2];
            send_bits(s, dist, extra);
          }
        }
      } while (sx < s.sym_next);
    }
    send_code(s, END_BLOCK2, ltree);
  };
  var build_tree = (s, desc) => {
    const tree = desc.dyn_tree;
    const stree = desc.stat_desc.static_tree;
    const has_stree = desc.stat_desc.has_stree;
    const elems = desc.stat_desc.elems;
    let n, m;
    let max_code = -1;
    let node;
    s.heap_len = 0;
    s.heap_max = HEAP_SIZE$1;
    for (n = 0; n < elems; n++) {
      if (tree[n * 2] !== 0) {
        s.heap[++s.heap_len] = max_code = n;
        s.depth[n] = 0;
      } else {
        tree[n * 2 + 1] = 0;
      }
    }
    while (s.heap_len < 2) {
      node = s.heap[++s.heap_len] = max_code < 2 ? ++max_code : 0;
      tree[node * 2] = 1;
      s.depth[node] = 0;
      s.opt_len--;
      if (has_stree) {
        s.static_len -= stree[node * 2 + 1];
      }
    }
    desc.max_code = max_code;
    for (n = s.heap_len >> 1; n >= 1; n--) {
      pqdownheap(s, tree, n);
    }
    node = elems;
    do {
      n = s.heap[
        1
        /*SMALLEST*/
      ];
      s.heap[
        1
        /*SMALLEST*/
      ] = s.heap[s.heap_len--];
      pqdownheap(
        s,
        tree,
        1
        /*SMALLEST*/
      );
      m = s.heap[
        1
        /*SMALLEST*/
      ];
      s.heap[--s.heap_max] = n;
      s.heap[--s.heap_max] = m;
      tree[node * 2] = tree[n * 2] + tree[m * 2];
      s.depth[node] = (s.depth[n] >= s.depth[m] ? s.depth[n] : s.depth[m]) + 1;
      tree[n * 2 + 1] = tree[m * 2 + 1] = node;
      s.heap[
        1
        /*SMALLEST*/
      ] = node++;
      pqdownheap(
        s,
        tree,
        1
        /*SMALLEST*/
      );
    } while (s.heap_len >= 2);
    s.heap[--s.heap_max] = s.heap[
      1
      /*SMALLEST*/
    ];
    gen_bitlen(s, desc);
    gen_codes(tree, max_code, s.bl_count);
  };
  var scan_tree = (s, tree, max_code) => {
    let n;
    let prevlen = -1;
    let curlen;
    let nextlen = tree[0 * 2 + 1];
    let count = 0;
    let max_count = 7;
    let min_count = 4;
    if (nextlen === 0) {
      max_count = 138;
      min_count = 3;
    }
    tree[(max_code + 1) * 2 + 1] = 65535;
    for (n = 0; n <= max_code; n++) {
      curlen = nextlen;
      nextlen = tree[(n + 1) * 2 + 1];
      if (++count < max_count && curlen === nextlen) {
        continue;
      } else if (count < min_count) {
        s.bl_tree[curlen * 2] += count;
      } else if (curlen !== 0) {
        if (curlen !== prevlen) {
          s.bl_tree[curlen * 2]++;
        }
        s.bl_tree[REP_3_62 * 2]++;
      } else if (count <= 10) {
        s.bl_tree[REPZ_3_102 * 2]++;
      } else {
        s.bl_tree[REPZ_11_1382 * 2]++;
      }
      count = 0;
      prevlen = curlen;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      } else if (curlen === nextlen) {
        max_count = 6;
        min_count = 3;
      } else {
        max_count = 7;
        min_count = 4;
      }
    }
  };
  var send_tree = (s, tree, max_code) => {
    let n;
    let prevlen = -1;
    let curlen;
    let nextlen = tree[0 * 2 + 1];
    let count = 0;
    let max_count = 7;
    let min_count = 4;
    if (nextlen === 0) {
      max_count = 138;
      min_count = 3;
    }
    for (n = 0; n <= max_code; n++) {
      curlen = nextlen;
      nextlen = tree[(n + 1) * 2 + 1];
      if (++count < max_count && curlen === nextlen) {
        continue;
      } else if (count < min_count) {
        do {
          send_code(s, curlen, s.bl_tree);
        } while (--count !== 0);
      } else if (curlen !== 0) {
        if (curlen !== prevlen) {
          send_code(s, curlen, s.bl_tree);
          count--;
        }
        send_code(s, REP_3_62, s.bl_tree);
        send_bits(s, count - 3, 2);
      } else if (count <= 10) {
        send_code(s, REPZ_3_102, s.bl_tree);
        send_bits(s, count - 3, 3);
      } else {
        send_code(s, REPZ_11_1382, s.bl_tree);
        send_bits(s, count - 11, 7);
      }
      count = 0;
      prevlen = curlen;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      } else if (curlen === nextlen) {
        max_count = 6;
        min_count = 3;
      } else {
        max_count = 7;
        min_count = 4;
      }
    }
  };
  var build_bl_tree = (s) => {
    let max_blindex;
    scan_tree(s, s.dyn_ltree, s.l_desc.max_code);
    scan_tree(s, s.dyn_dtree, s.d_desc.max_code);
    build_tree(s, s.bl_desc);
    for (max_blindex = BL_CODES$1 - 1; max_blindex >= 3; max_blindex--) {
      if (s.bl_tree[bl_order[max_blindex] * 2 + 1] !== 0) {
        break;
      }
    }
    s.opt_len += 3 * (max_blindex + 1) + 5 + 5 + 4;
    return max_blindex;
  };
  var send_all_trees = (s, lcodes, dcodes, blcodes) => {
    let rank2;
    send_bits(s, lcodes - 257, 5);
    send_bits(s, dcodes - 1, 5);
    send_bits(s, blcodes - 4, 4);
    for (rank2 = 0; rank2 < blcodes; rank2++) {
      send_bits(s, s.bl_tree[bl_order[rank2] * 2 + 1], 3);
    }
    send_tree(s, s.dyn_ltree, lcodes - 1);
    send_tree(s, s.dyn_dtree, dcodes - 1);
  };
  var detect_data_type = (s) => {
    let block_mask = 4093624447;
    let n;
    for (n = 0; n <= 31; n++, block_mask >>>= 1) {
      if (block_mask & 1 && s.dyn_ltree[n * 2] !== 0) {
        return Z_BINARY;
      }
    }
    if (s.dyn_ltree[9 * 2] !== 0 || s.dyn_ltree[10 * 2] !== 0 || s.dyn_ltree[13 * 2] !== 0) {
      return Z_TEXT;
    }
    for (n = 32; n < LITERALS$1; n++) {
      if (s.dyn_ltree[n * 2] !== 0) {
        return Z_TEXT;
      }
    }
    return Z_BINARY;
  };
  var static_init_done = false;
  var _tr_init$1 = (s) => {
    if (!static_init_done) {
      tr_static_init();
      static_init_done = true;
    }
    s.l_desc = new TreeDesc(s.dyn_ltree, static_l_desc);
    s.d_desc = new TreeDesc(s.dyn_dtree, static_d_desc);
    s.bl_desc = new TreeDesc(s.bl_tree, static_bl_desc);
    s.bi_buf = 0;
    s.bi_valid = 0;
    init_block(s);
  };
  var _tr_stored_block$1 = (s, buf, stored_len, last) => {
    send_bits(s, (STORED_BLOCK2 << 1) + (last ? 1 : 0), 3);
    bi_windup(s);
    put_short(s, stored_len);
    put_short(s, ~stored_len);
    if (stored_len) {
      s.pending_buf.set(s.window.subarray(buf, buf + stored_len), s.pending);
    }
    s.pending += stored_len;
  };
  var _tr_align$1 = (s) => {
    send_bits(s, STATIC_TREES2 << 1, 3);
    send_code(s, END_BLOCK2, static_ltree);
    bi_flush(s);
  };
  var _tr_flush_block$1 = (s, buf, stored_len, last) => {
    let opt_lenb, static_lenb;
    let max_blindex = 0;
    if (s.level > 0) {
      if (s.strm.data_type === Z_UNKNOWN$1) {
        s.strm.data_type = detect_data_type(s);
      }
      build_tree(s, s.l_desc);
      build_tree(s, s.d_desc);
      max_blindex = build_bl_tree(s);
      opt_lenb = s.opt_len + 3 + 7 >>> 3;
      static_lenb = s.static_len + 3 + 7 >>> 3;
      if (static_lenb <= opt_lenb) {
        opt_lenb = static_lenb;
      }
    } else {
      opt_lenb = static_lenb = stored_len + 5;
    }
    if (stored_len + 4 <= opt_lenb && buf !== -1) {
      _tr_stored_block$1(s, buf, stored_len, last);
    } else if (s.strategy === Z_FIXED$1 || static_lenb === opt_lenb) {
      send_bits(s, (STATIC_TREES2 << 1) + (last ? 1 : 0), 3);
      compress_block(s, static_ltree, static_dtree);
    } else {
      send_bits(s, (DYN_TREES2 << 1) + (last ? 1 : 0), 3);
      send_all_trees(s, s.l_desc.max_code + 1, s.d_desc.max_code + 1, max_blindex + 1);
      compress_block(s, s.dyn_ltree, s.dyn_dtree);
    }
    init_block(s);
    if (last) {
      bi_windup(s);
    }
  };
  var _tr_tally$1 = (s, dist, lc) => {
    s.pending_buf[s.sym_buf + s.sym_next++] = dist;
    s.pending_buf[s.sym_buf + s.sym_next++] = dist >> 8;
    s.pending_buf[s.sym_buf + s.sym_next++] = lc;
    if (dist === 0) {
      s.dyn_ltree[lc * 2]++;
    } else {
      s.matches++;
      dist--;
      s.dyn_ltree[(_length_code[lc] + LITERALS$1 + 1) * 2]++;
      s.dyn_dtree[d_code(dist) * 2]++;
    }
    return s.sym_next === s.sym_end;
  };
  var _tr_init_1 = _tr_init$1;
  var _tr_stored_block_1 = _tr_stored_block$1;
  var _tr_flush_block_1 = _tr_flush_block$1;
  var _tr_tally_1 = _tr_tally$1;
  var _tr_align_1 = _tr_align$1;
  var trees = {
    _tr_init: _tr_init_1,
    _tr_stored_block: _tr_stored_block_1,
    _tr_flush_block: _tr_flush_block_1,
    _tr_tally: _tr_tally_1,
    _tr_align: _tr_align_1
  };
  var adler32 = (adler, buf, len, pos) => {
    let s1 = adler & 65535 | 0, s2 = adler >>> 16 & 65535 | 0, n = 0;
    while (len !== 0) {
      n = len > 2e3 ? 2e3 : len;
      len -= n;
      do {
        s1 = s1 + buf[pos++] | 0;
        s2 = s2 + s1 | 0;
      } while (--n);
      s1 %= 65521;
      s2 %= 65521;
    }
    return s1 | s2 << 16 | 0;
  };
  var adler32_1 = adler32;
  var makeTable = () => {
    let c, table3 = [];
    for (var n = 0; n < 256; n++) {
      c = n;
      for (var k = 0; k < 8; k++) {
        c = c & 1 ? 3988292384 ^ c >>> 1 : c >>> 1;
      }
      table3[n] = c;
    }
    return table3;
  };
  var crcTable = new Uint32Array(makeTable());
  var crc32 = (crc, buf, len, pos) => {
    const t = crcTable;
    const end = pos + len;
    crc ^= -1;
    for (let i = pos; i < end; i++) {
      crc = crc >>> 8 ^ t[(crc ^ buf[i]) & 255];
    }
    return crc ^ -1;
  };
  var crc32_1 = crc32;
  var messages = {
    2: "need dictionary",
    /* Z_NEED_DICT       2  */
    1: "stream end",
    /* Z_STREAM_END      1  */
    0: "",
    /* Z_OK              0  */
    "-1": "file error",
    /* Z_ERRNO         (-1) */
    "-2": "stream error",
    /* Z_STREAM_ERROR  (-2) */
    "-3": "data error",
    /* Z_DATA_ERROR    (-3) */
    "-4": "insufficient memory",
    /* Z_MEM_ERROR     (-4) */
    "-5": "buffer error",
    /* Z_BUF_ERROR     (-5) */
    "-6": "incompatible version"
    /* Z_VERSION_ERROR (-6) */
  };
  var constants$2 = {
    /* Allowed flush values; see deflate() and inflate() below for details */
    Z_NO_FLUSH: 0,
    Z_PARTIAL_FLUSH: 1,
    Z_SYNC_FLUSH: 2,
    Z_FULL_FLUSH: 3,
    Z_FINISH: 4,
    Z_BLOCK: 5,
    Z_TREES: 6,
    /* Return codes for the compression/decompression functions. Negative values
    * are errors, positive values are used for special but normal events.
    */
    Z_OK: 0,
    Z_STREAM_END: 1,
    Z_NEED_DICT: 2,
    Z_ERRNO: -1,
    Z_STREAM_ERROR: -2,
    Z_DATA_ERROR: -3,
    Z_MEM_ERROR: -4,
    Z_BUF_ERROR: -5,
    //Z_VERSION_ERROR: -6,
    /* compression levels */
    Z_NO_COMPRESSION: 0,
    Z_BEST_SPEED: 1,
    Z_BEST_COMPRESSION: 9,
    Z_DEFAULT_COMPRESSION: -1,
    Z_FILTERED: 1,
    Z_HUFFMAN_ONLY: 2,
    Z_RLE: 3,
    Z_FIXED: 4,
    Z_DEFAULT_STRATEGY: 0,
    /* Possible values of the data_type field (though see inflate()) */
    Z_BINARY: 0,
    Z_TEXT: 1,
    //Z_ASCII:                1, // = Z_TEXT (deprecated)
    Z_UNKNOWN: 2,
    /* The deflate compression method */
    Z_DEFLATED: 8
    //Z_NULL:                 null // Use -1 or null inline, depending on var type
  };
  var { _tr_init, _tr_stored_block, _tr_flush_block, _tr_tally, _tr_align } = trees;
  var {
    Z_NO_FLUSH: Z_NO_FLUSH$2,
    Z_PARTIAL_FLUSH: Z_PARTIAL_FLUSH2,
    Z_FULL_FLUSH: Z_FULL_FLUSH$1,
    Z_FINISH: Z_FINISH$3,
    Z_BLOCK: Z_BLOCK$1,
    Z_OK: Z_OK$3,
    Z_STREAM_END: Z_STREAM_END$3,
    Z_STREAM_ERROR: Z_STREAM_ERROR$2,
    Z_DATA_ERROR: Z_DATA_ERROR$2,
    Z_BUF_ERROR: Z_BUF_ERROR$1,
    Z_DEFAULT_COMPRESSION: Z_DEFAULT_COMPRESSION$1,
    Z_FILTERED: Z_FILTERED2,
    Z_HUFFMAN_ONLY: Z_HUFFMAN_ONLY2,
    Z_RLE,
    Z_FIXED,
    Z_DEFAULT_STRATEGY: Z_DEFAULT_STRATEGY$1,
    Z_UNKNOWN,
    Z_DEFLATED: Z_DEFLATED$2
  } = constants$2;
  var MAX_MEM_LEVEL2 = 9;
  var MAX_WBITS$1 = 15;
  var DEF_MEM_LEVEL2 = 8;
  var LENGTH_CODES2 = 29;
  var LITERALS2 = 256;
  var L_CODES2 = LITERALS2 + 1 + LENGTH_CODES2;
  var D_CODES2 = 30;
  var BL_CODES2 = 19;
  var HEAP_SIZE2 = 2 * L_CODES2 + 1;
  var MAX_BITS3 = 15;
  var MIN_MATCH2 = 3;
  var MAX_MATCH2 = 258;
  var MIN_LOOKAHEAD2 = MAX_MATCH2 + MIN_MATCH2 + 1;
  var PRESET_DICT3 = 32;
  var INIT_STATE2 = 42;
  var GZIP_STATE = 57;
  var EXTRA_STATE = 69;
  var NAME_STATE = 73;
  var COMMENT_STATE = 91;
  var HCRC_STATE = 103;
  var BUSY_STATE2 = 113;
  var FINISH_STATE2 = 666;
  var BS_NEED_MORE = 1;
  var BS_BLOCK_DONE = 2;
  var BS_FINISH_STARTED = 3;
  var BS_FINISH_DONE = 4;
  var OS_CODE = 3;
  var err = (strm, errorCode) => {
    strm.msg = messages[errorCode];
    return errorCode;
  };
  var rank = (f) => {
    return f * 2 - (f > 4 ? 9 : 0);
  };
  var zero = (buf) => {
    let len = buf.length;
    while (--len >= 0) {
      buf[len] = 0;
    }
  };
  var slide_hash = (s) => {
    let n, m;
    let p;
    let wsize = s.w_size;
    n = s.hash_size;
    p = n;
    do {
      m = s.head[--p];
      s.head[p] = m >= wsize ? m - wsize : 0;
    } while (--n);
    n = wsize;
    p = n;
    do {
      m = s.prev[--p];
      s.prev[p] = m >= wsize ? m - wsize : 0;
    } while (--n);
  };
  var HASH_ZLIB = (s, prev, data) => (prev << s.hash_shift ^ data) & s.hash_mask;
  var HASH = HASH_ZLIB;
  var flush_pending = (strm) => {
    const s = strm.state;
    let len = s.pending;
    if (len > strm.avail_out) {
      len = strm.avail_out;
    }
    if (len === 0) {
      return;
    }
    strm.output.set(s.pending_buf.subarray(s.pending_out, s.pending_out + len), strm.next_out);
    strm.next_out += len;
    s.pending_out += len;
    strm.total_out += len;
    strm.avail_out -= len;
    s.pending -= len;
    if (s.pending === 0) {
      s.pending_out = 0;
    }
  };
  var flush_block_only = (s, last) => {
    _tr_flush_block(s, s.block_start >= 0 ? s.block_start : -1, s.strstart - s.block_start, last);
    s.block_start = s.strstart;
    flush_pending(s.strm);
  };
  var put_byte = (s, b) => {
    s.pending_buf[s.pending++] = b;
  };
  var putShortMSB = (s, b) => {
    s.pending_buf[s.pending++] = b >>> 8 & 255;
    s.pending_buf[s.pending++] = b & 255;
  };
  var read_buf = (strm, buf, start, size) => {
    let len = strm.avail_in;
    if (len > size) {
      len = size;
    }
    if (len === 0) {
      return 0;
    }
    strm.avail_in -= len;
    buf.set(strm.input.subarray(strm.next_in, strm.next_in + len), start);
    if (strm.state.wrap === 1) {
      strm.adler = adler32_1(strm.adler, buf, len, start);
    } else if (strm.state.wrap === 2) {
      strm.adler = crc32_1(strm.adler, buf, len, start);
    }
    strm.next_in += len;
    strm.total_in += len;
    return len;
  };
  var longest_match = (s, cur_match) => {
    let chain_length = s.max_chain_length;
    let scan = s.strstart;
    let match;
    let len;
    let best_len = s.prev_length;
    let nice_match = s.nice_match;
    const limit = s.strstart > s.w_size - MIN_LOOKAHEAD2 ? s.strstart - (s.w_size - MIN_LOOKAHEAD2) : 0;
    const _win = s.window;
    const wmask = s.w_mask;
    const prev = s.prev;
    const strend = s.strstart + MAX_MATCH2;
    let scan_end1 = _win[scan + best_len - 1];
    let scan_end = _win[scan + best_len];
    if (s.prev_length >= s.good_match) {
      chain_length >>= 2;
    }
    if (nice_match > s.lookahead) {
      nice_match = s.lookahead;
    }
    do {
      match = cur_match;
      if (_win[match + best_len] !== scan_end || _win[match + best_len - 1] !== scan_end1 || _win[match] !== _win[scan] || _win[++match] !== _win[scan + 1]) {
        continue;
      }
      scan += 2;
      match++;
      do {
      } while (_win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && _win[++scan] === _win[++match] && scan < strend);
      len = MAX_MATCH2 - (strend - scan);
      scan = strend - MAX_MATCH2;
      if (len > best_len) {
        s.match_start = cur_match;
        best_len = len;
        if (len >= nice_match) {
          break;
        }
        scan_end1 = _win[scan + best_len - 1];
        scan_end = _win[scan + best_len];
      }
    } while ((cur_match = prev[cur_match & wmask]) > limit && --chain_length !== 0);
    if (best_len <= s.lookahead) {
      return best_len;
    }
    return s.lookahead;
  };
  var fill_window = (s) => {
    const _w_size = s.w_size;
    let n, more, str;
    do {
      more = s.window_size - s.lookahead - s.strstart;
      if (s.strstart >= _w_size + (_w_size - MIN_LOOKAHEAD2)) {
        s.window.set(s.window.subarray(_w_size, _w_size + _w_size - more), 0);
        s.match_start -= _w_size;
        s.strstart -= _w_size;
        s.block_start -= _w_size;
        if (s.insert > s.strstart) {
          s.insert = s.strstart;
        }
        slide_hash(s);
        more += _w_size;
      }
      if (s.strm.avail_in === 0) {
        break;
      }
      n = read_buf(s.strm, s.window, s.strstart + s.lookahead, more);
      s.lookahead += n;
      if (s.lookahead + s.insert >= MIN_MATCH2) {
        str = s.strstart - s.insert;
        s.ins_h = s.window[str];
        s.ins_h = HASH(s, s.ins_h, s.window[str + 1]);
        while (s.insert) {
          s.ins_h = HASH(s, s.ins_h, s.window[str + MIN_MATCH2 - 1]);
          s.prev[str & s.w_mask] = s.head[s.ins_h];
          s.head[s.ins_h] = str;
          str++;
          s.insert--;
          if (s.lookahead + s.insert < MIN_MATCH2) {
            break;
          }
        }
      }
    } while (s.lookahead < MIN_LOOKAHEAD2 && s.strm.avail_in !== 0);
  };
  var deflate_stored = (s, flush) => {
    let min_block = s.pending_buf_size - 5 > s.w_size ? s.w_size : s.pending_buf_size - 5;
    let len, left, have, last = 0;
    let used = s.strm.avail_in;
    do {
      len = 65535;
      have = s.bi_valid + 42 >> 3;
      if (s.strm.avail_out < have) {
        break;
      }
      have = s.strm.avail_out - have;
      left = s.strstart - s.block_start;
      if (len > left + s.strm.avail_in) {
        len = left + s.strm.avail_in;
      }
      if (len > have) {
        len = have;
      }
      if (len < min_block && (len === 0 && flush !== Z_FINISH$3 || flush === Z_NO_FLUSH$2 || len !== left + s.strm.avail_in)) {
        break;
      }
      last = flush === Z_FINISH$3 && len === left + s.strm.avail_in ? 1 : 0;
      _tr_stored_block(s, 0, 0, last);
      s.pending_buf[s.pending - 4] = len;
      s.pending_buf[s.pending - 3] = len >> 8;
      s.pending_buf[s.pending - 2] = ~len;
      s.pending_buf[s.pending - 1] = ~len >> 8;
      flush_pending(s.strm);
      if (left) {
        if (left > len) {
          left = len;
        }
        s.strm.output.set(s.window.subarray(s.block_start, s.block_start + left), s.strm.next_out);
        s.strm.next_out += left;
        s.strm.avail_out -= left;
        s.strm.total_out += left;
        s.block_start += left;
        len -= left;
      }
      if (len) {
        read_buf(s.strm, s.strm.output, s.strm.next_out, len);
        s.strm.next_out += len;
        s.strm.avail_out -= len;
        s.strm.total_out += len;
      }
    } while (last === 0);
    used -= s.strm.avail_in;
    if (used) {
      if (used >= s.w_size) {
        s.matches = 2;
        s.window.set(s.strm.input.subarray(s.strm.next_in - s.w_size, s.strm.next_in), 0);
        s.strstart = s.w_size;
        s.insert = s.strstart;
      } else {
        if (s.window_size - s.strstart <= used) {
          s.strstart -= s.w_size;
          s.window.set(s.window.subarray(s.w_size, s.w_size + s.strstart), 0);
          if (s.matches < 2) {
            s.matches++;
          }
          if (s.insert > s.strstart) {
            s.insert = s.strstart;
          }
        }
        s.window.set(s.strm.input.subarray(s.strm.next_in - used, s.strm.next_in), s.strstart);
        s.strstart += used;
        s.insert += used > s.w_size - s.insert ? s.w_size - s.insert : used;
      }
      s.block_start = s.strstart;
    }
    if (s.high_water < s.strstart) {
      s.high_water = s.strstart;
    }
    if (last) {
      return BS_FINISH_DONE;
    }
    if (flush !== Z_NO_FLUSH$2 && flush !== Z_FINISH$3 && s.strm.avail_in === 0 && s.strstart === s.block_start) {
      return BS_BLOCK_DONE;
    }
    have = s.window_size - s.strstart;
    if (s.strm.avail_in > have && s.block_start >= s.w_size) {
      s.block_start -= s.w_size;
      s.strstart -= s.w_size;
      s.window.set(s.window.subarray(s.w_size, s.w_size + s.strstart), 0);
      if (s.matches < 2) {
        s.matches++;
      }
      have += s.w_size;
      if (s.insert > s.strstart) {
        s.insert = s.strstart;
      }
    }
    if (have > s.strm.avail_in) {
      have = s.strm.avail_in;
    }
    if (have) {
      read_buf(s.strm, s.window, s.strstart, have);
      s.strstart += have;
      s.insert += have > s.w_size - s.insert ? s.w_size - s.insert : have;
    }
    if (s.high_water < s.strstart) {
      s.high_water = s.strstart;
    }
    have = s.bi_valid + 42 >> 3;
    have = s.pending_buf_size - have > 65535 ? 65535 : s.pending_buf_size - have;
    min_block = have > s.w_size ? s.w_size : have;
    left = s.strstart - s.block_start;
    if (left >= min_block || (left || flush === Z_FINISH$3) && flush !== Z_NO_FLUSH$2 && s.strm.avail_in === 0 && left <= have) {
      len = left > have ? have : left;
      last = flush === Z_FINISH$3 && s.strm.avail_in === 0 && len === left ? 1 : 0;
      _tr_stored_block(s, s.block_start, len, last);
      s.block_start += len;
      flush_pending(s.strm);
    }
    return last ? BS_FINISH_STARTED : BS_NEED_MORE;
  };
  var deflate_fast = (s, flush) => {
    let hash_head;
    let bflush;
    for (; ; ) {
      if (s.lookahead < MIN_LOOKAHEAD2) {
        fill_window(s);
        if (s.lookahead < MIN_LOOKAHEAD2 && flush === Z_NO_FLUSH$2) {
          return BS_NEED_MORE;
        }
        if (s.lookahead === 0) {
          break;
        }
      }
      hash_head = 0;
      if (s.lookahead >= MIN_MATCH2) {
        s.ins_h = HASH(s, s.ins_h, s.window[s.strstart + MIN_MATCH2 - 1]);
        hash_head = s.prev[s.strstart & s.w_mask] = s.head[s.ins_h];
        s.head[s.ins_h] = s.strstart;
      }
      if (hash_head !== 0 && s.strstart - hash_head <= s.w_size - MIN_LOOKAHEAD2) {
        s.match_length = longest_match(s, hash_head);
      }
      if (s.match_length >= MIN_MATCH2) {
        bflush = _tr_tally(s, s.strstart - s.match_start, s.match_length - MIN_MATCH2);
        s.lookahead -= s.match_length;
        if (s.match_length <= s.max_lazy_match && s.lookahead >= MIN_MATCH2) {
          s.match_length--;
          do {
            s.strstart++;
            s.ins_h = HASH(s, s.ins_h, s.window[s.strstart + MIN_MATCH2 - 1]);
            hash_head = s.prev[s.strstart & s.w_mask] = s.head[s.ins_h];
            s.head[s.ins_h] = s.strstart;
          } while (--s.match_length !== 0);
          s.strstart++;
        } else {
          s.strstart += s.match_length;
          s.match_length = 0;
          s.ins_h = s.window[s.strstart];
          s.ins_h = HASH(s, s.ins_h, s.window[s.strstart + 1]);
        }
      } else {
        bflush = _tr_tally(s, 0, s.window[s.strstart]);
        s.lookahead--;
        s.strstart++;
      }
      if (bflush) {
        flush_block_only(s, false);
        if (s.strm.avail_out === 0) {
          return BS_NEED_MORE;
        }
      }
    }
    s.insert = s.strstart < MIN_MATCH2 - 1 ? s.strstart : MIN_MATCH2 - 1;
    if (flush === Z_FINISH$3) {
      flush_block_only(s, true);
      if (s.strm.avail_out === 0) {
        return BS_FINISH_STARTED;
      }
      return BS_FINISH_DONE;
    }
    if (s.sym_next) {
      flush_block_only(s, false);
      if (s.strm.avail_out === 0) {
        return BS_NEED_MORE;
      }
    }
    return BS_BLOCK_DONE;
  };
  var deflate_slow = (s, flush) => {
    let hash_head;
    let bflush;
    let max_insert;
    for (; ; ) {
      if (s.lookahead < MIN_LOOKAHEAD2) {
        fill_window(s);
        if (s.lookahead < MIN_LOOKAHEAD2 && flush === Z_NO_FLUSH$2) {
          return BS_NEED_MORE;
        }
        if (s.lookahead === 0) {
          break;
        }
      }
      hash_head = 0;
      if (s.lookahead >= MIN_MATCH2) {
        s.ins_h = HASH(s, s.ins_h, s.window[s.strstart + MIN_MATCH2 - 1]);
        hash_head = s.prev[s.strstart & s.w_mask] = s.head[s.ins_h];
        s.head[s.ins_h] = s.strstart;
      }
      s.prev_length = s.match_length;
      s.prev_match = s.match_start;
      s.match_length = MIN_MATCH2 - 1;
      if (hash_head !== 0 && s.prev_length < s.max_lazy_match && s.strstart - hash_head <= s.w_size - MIN_LOOKAHEAD2) {
        s.match_length = longest_match(s, hash_head);
        if (s.match_length <= 5 && (s.strategy === Z_FILTERED2 || s.match_length === MIN_MATCH2 && s.strstart - s.match_start > 4096)) {
          s.match_length = MIN_MATCH2 - 1;
        }
      }
      if (s.prev_length >= MIN_MATCH2 && s.match_length <= s.prev_length) {
        max_insert = s.strstart + s.lookahead - MIN_MATCH2;
        bflush = _tr_tally(s, s.strstart - 1 - s.prev_match, s.prev_length - MIN_MATCH2);
        s.lookahead -= s.prev_length - 1;
        s.prev_length -= 2;
        do {
          if (++s.strstart <= max_insert) {
            s.ins_h = HASH(s, s.ins_h, s.window[s.strstart + MIN_MATCH2 - 1]);
            hash_head = s.prev[s.strstart & s.w_mask] = s.head[s.ins_h];
            s.head[s.ins_h] = s.strstart;
          }
        } while (--s.prev_length !== 0);
        s.match_available = 0;
        s.match_length = MIN_MATCH2 - 1;
        s.strstart++;
        if (bflush) {
          flush_block_only(s, false);
          if (s.strm.avail_out === 0) {
            return BS_NEED_MORE;
          }
        }
      } else if (s.match_available) {
        bflush = _tr_tally(s, 0, s.window[s.strstart - 1]);
        if (bflush) {
          flush_block_only(s, false);
        }
        s.strstart++;
        s.lookahead--;
        if (s.strm.avail_out === 0) {
          return BS_NEED_MORE;
        }
      } else {
        s.match_available = 1;
        s.strstart++;
        s.lookahead--;
      }
    }
    if (s.match_available) {
      bflush = _tr_tally(s, 0, s.window[s.strstart - 1]);
      s.match_available = 0;
    }
    s.insert = s.strstart < MIN_MATCH2 - 1 ? s.strstart : MIN_MATCH2 - 1;
    if (flush === Z_FINISH$3) {
      flush_block_only(s, true);
      if (s.strm.avail_out === 0) {
        return BS_FINISH_STARTED;
      }
      return BS_FINISH_DONE;
    }
    if (s.sym_next) {
      flush_block_only(s, false);
      if (s.strm.avail_out === 0) {
        return BS_NEED_MORE;
      }
    }
    return BS_BLOCK_DONE;
  };
  var deflate_rle = (s, flush) => {
    let bflush;
    let prev;
    let scan, strend;
    const _win = s.window;
    for (; ; ) {
      if (s.lookahead <= MAX_MATCH2) {
        fill_window(s);
        if (s.lookahead <= MAX_MATCH2 && flush === Z_NO_FLUSH$2) {
          return BS_NEED_MORE;
        }
        if (s.lookahead === 0) {
          break;
        }
      }
      s.match_length = 0;
      if (s.lookahead >= MIN_MATCH2 && s.strstart > 0) {
        scan = s.strstart - 1;
        prev = _win[scan];
        if (prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan]) {
          strend = s.strstart + MAX_MATCH2;
          do {
          } while (prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && prev === _win[++scan] && scan < strend);
          s.match_length = MAX_MATCH2 - (strend - scan);
          if (s.match_length > s.lookahead) {
            s.match_length = s.lookahead;
          }
        }
      }
      if (s.match_length >= MIN_MATCH2) {
        bflush = _tr_tally(s, 1, s.match_length - MIN_MATCH2);
        s.lookahead -= s.match_length;
        s.strstart += s.match_length;
        s.match_length = 0;
      } else {
        bflush = _tr_tally(s, 0, s.window[s.strstart]);
        s.lookahead--;
        s.strstart++;
      }
      if (bflush) {
        flush_block_only(s, false);
        if (s.strm.avail_out === 0) {
          return BS_NEED_MORE;
        }
      }
    }
    s.insert = 0;
    if (flush === Z_FINISH$3) {
      flush_block_only(s, true);
      if (s.strm.avail_out === 0) {
        return BS_FINISH_STARTED;
      }
      return BS_FINISH_DONE;
    }
    if (s.sym_next) {
      flush_block_only(s, false);
      if (s.strm.avail_out === 0) {
        return BS_NEED_MORE;
      }
    }
    return BS_BLOCK_DONE;
  };
  var deflate_huff = (s, flush) => {
    let bflush;
    for (; ; ) {
      if (s.lookahead === 0) {
        fill_window(s);
        if (s.lookahead === 0) {
          if (flush === Z_NO_FLUSH$2) {
            return BS_NEED_MORE;
          }
          break;
        }
      }
      s.match_length = 0;
      bflush = _tr_tally(s, 0, s.window[s.strstart]);
      s.lookahead--;
      s.strstart++;
      if (bflush) {
        flush_block_only(s, false);
        if (s.strm.avail_out === 0) {
          return BS_NEED_MORE;
        }
      }
    }
    s.insert = 0;
    if (flush === Z_FINISH$3) {
      flush_block_only(s, true);
      if (s.strm.avail_out === 0) {
        return BS_FINISH_STARTED;
      }
      return BS_FINISH_DONE;
    }
    if (s.sym_next) {
      flush_block_only(s, false);
      if (s.strm.avail_out === 0) {
        return BS_NEED_MORE;
      }
    }
    return BS_BLOCK_DONE;
  };
  function Config2(good_length, max_lazy, nice_length, max_chain, func) {
    this.good_length = good_length;
    this.max_lazy = max_lazy;
    this.nice_length = nice_length;
    this.max_chain = max_chain;
    this.func = func;
  }
  var configuration_table = [
    /*      good lazy nice chain */
    new Config2(0, 0, 0, 0, deflate_stored),
    /* 0 store only */
    new Config2(4, 4, 8, 4, deflate_fast),
    /* 1 max speed, no lazy matches */
    new Config2(4, 5, 16, 8, deflate_fast),
    /* 2 */
    new Config2(4, 6, 32, 32, deflate_fast),
    /* 3 */
    new Config2(4, 4, 16, 16, deflate_slow),
    /* 4 lazy matches */
    new Config2(8, 16, 32, 32, deflate_slow),
    /* 5 */
    new Config2(8, 16, 128, 128, deflate_slow),
    /* 6 */
    new Config2(8, 32, 128, 256, deflate_slow),
    /* 7 */
    new Config2(32, 128, 258, 1024, deflate_slow),
    /* 8 */
    new Config2(32, 258, 258, 4096, deflate_slow)
    /* 9 max compression */
  ];
  var lm_init = (s) => {
    s.window_size = 2 * s.w_size;
    zero(s.head);
    s.max_lazy_match = configuration_table[s.level].max_lazy;
    s.good_match = configuration_table[s.level].good_length;
    s.nice_match = configuration_table[s.level].nice_length;
    s.max_chain_length = configuration_table[s.level].max_chain;
    s.strstart = 0;
    s.block_start = 0;
    s.lookahead = 0;
    s.insert = 0;
    s.match_length = s.prev_length = MIN_MATCH2 - 1;
    s.match_available = 0;
    s.ins_h = 0;
  };
  function DeflateState() {
    this.strm = null;
    this.status = 0;
    this.pending_buf = null;
    this.pending_buf_size = 0;
    this.pending_out = 0;
    this.pending = 0;
    this.wrap = 0;
    this.gzhead = null;
    this.gzindex = 0;
    this.method = Z_DEFLATED$2;
    this.last_flush = -1;
    this.w_size = 0;
    this.w_bits = 0;
    this.w_mask = 0;
    this.window = null;
    this.window_size = 0;
    this.prev = null;
    this.head = null;
    this.ins_h = 0;
    this.hash_size = 0;
    this.hash_bits = 0;
    this.hash_mask = 0;
    this.hash_shift = 0;
    this.block_start = 0;
    this.match_length = 0;
    this.prev_match = 0;
    this.match_available = 0;
    this.strstart = 0;
    this.match_start = 0;
    this.lookahead = 0;
    this.prev_length = 0;
    this.max_chain_length = 0;
    this.max_lazy_match = 0;
    this.level = 0;
    this.strategy = 0;
    this.good_match = 0;
    this.nice_match = 0;
    this.dyn_ltree = new Uint16Array(HEAP_SIZE2 * 2);
    this.dyn_dtree = new Uint16Array((2 * D_CODES2 + 1) * 2);
    this.bl_tree = new Uint16Array((2 * BL_CODES2 + 1) * 2);
    zero(this.dyn_ltree);
    zero(this.dyn_dtree);
    zero(this.bl_tree);
    this.l_desc = null;
    this.d_desc = null;
    this.bl_desc = null;
    this.bl_count = new Uint16Array(MAX_BITS3 + 1);
    this.heap = new Uint16Array(2 * L_CODES2 + 1);
    zero(this.heap);
    this.heap_len = 0;
    this.heap_max = 0;
    this.depth = new Uint16Array(2 * L_CODES2 + 1);
    zero(this.depth);
    this.sym_buf = 0;
    this.lit_bufsize = 0;
    this.sym_next = 0;
    this.sym_end = 0;
    this.opt_len = 0;
    this.static_len = 0;
    this.matches = 0;
    this.insert = 0;
    this.bi_buf = 0;
    this.bi_valid = 0;
  }
  var deflateStateCheck = (strm) => {
    if (!strm) {
      return 1;
    }
    const s = strm.state;
    if (!s || s.strm !== strm || s.status !== INIT_STATE2 && //#ifdef GZIP
    s.status !== GZIP_STATE && //#endif
    s.status !== EXTRA_STATE && s.status !== NAME_STATE && s.status !== COMMENT_STATE && s.status !== HCRC_STATE && s.status !== BUSY_STATE2 && s.status !== FINISH_STATE2) {
      return 1;
    }
    return 0;
  };
  var deflateResetKeep = (strm) => {
    if (deflateStateCheck(strm)) {
      return err(strm, Z_STREAM_ERROR$2);
    }
    strm.total_in = strm.total_out = 0;
    strm.data_type = Z_UNKNOWN;
    const s = strm.state;
    s.pending = 0;
    s.pending_out = 0;
    if (s.wrap < 0) {
      s.wrap = -s.wrap;
    }
    s.status = //#ifdef GZIP
    s.wrap === 2 ? GZIP_STATE : (
      //#endif
      s.wrap ? INIT_STATE2 : BUSY_STATE2
    );
    strm.adler = s.wrap === 2 ? 0 : 1;
    s.last_flush = -2;
    _tr_init(s);
    return Z_OK$3;
  };
  var deflateReset = (strm) => {
    const ret = deflateResetKeep(strm);
    if (ret === Z_OK$3) {
      lm_init(strm.state);
    }
    return ret;
  };
  var deflateSetHeader = (strm, head) => {
    if (deflateStateCheck(strm) || strm.state.wrap !== 2) {
      return Z_STREAM_ERROR$2;
    }
    strm.state.gzhead = head;
    return Z_OK$3;
  };
  var deflateInit2 = (strm, level, method, windowBits, memLevel, strategy) => {
    if (!strm) {
      return Z_STREAM_ERROR$2;
    }
    let wrap = 1;
    if (level === Z_DEFAULT_COMPRESSION$1) {
      level = 6;
    }
    if (windowBits < 0) {
      wrap = 0;
      windowBits = -windowBits;
    } else if (windowBits > 15) {
      wrap = 2;
      windowBits -= 16;
    }
    if (memLevel < 1 || memLevel > MAX_MEM_LEVEL2 || method !== Z_DEFLATED$2 || windowBits < 8 || windowBits > 15 || level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED || windowBits === 8 && wrap !== 1) {
      return err(strm, Z_STREAM_ERROR$2);
    }
    if (windowBits === 8) {
      windowBits = 9;
    }
    const s = new DeflateState();
    strm.state = s;
    s.strm = strm;
    s.status = INIT_STATE2;
    s.wrap = wrap;
    s.gzhead = null;
    s.w_bits = windowBits;
    s.w_size = 1 << s.w_bits;
    s.w_mask = s.w_size - 1;
    s.hash_bits = memLevel + 7;
    s.hash_size = 1 << s.hash_bits;
    s.hash_mask = s.hash_size - 1;
    s.hash_shift = ~~((s.hash_bits + MIN_MATCH2 - 1) / MIN_MATCH2);
    s.window = new Uint8Array(s.w_size * 2);
    s.head = new Uint16Array(s.hash_size);
    s.prev = new Uint16Array(s.w_size);
    s.lit_bufsize = 1 << memLevel + 6;
    s.pending_buf_size = s.lit_bufsize * 4;
    s.pending_buf = new Uint8Array(s.pending_buf_size);
    s.sym_buf = s.lit_bufsize;
    s.sym_end = (s.lit_bufsize - 1) * 3;
    s.level = level;
    s.strategy = strategy;
    s.method = method;
    return deflateReset(strm);
  };
  var deflateInit = (strm, level) => {
    return deflateInit2(strm, level, Z_DEFLATED$2, MAX_WBITS$1, DEF_MEM_LEVEL2, Z_DEFAULT_STRATEGY$1);
  };
  var deflate$2 = (strm, flush) => {
    if (deflateStateCheck(strm) || flush > Z_BLOCK$1 || flush < 0) {
      return strm ? err(strm, Z_STREAM_ERROR$2) : Z_STREAM_ERROR$2;
    }
    const s = strm.state;
    if (!strm.output || strm.avail_in !== 0 && !strm.input || s.status === FINISH_STATE2 && flush !== Z_FINISH$3) {
      return err(strm, strm.avail_out === 0 ? Z_BUF_ERROR$1 : Z_STREAM_ERROR$2);
    }
    const old_flush = s.last_flush;
    s.last_flush = flush;
    if (s.pending !== 0) {
      flush_pending(strm);
      if (strm.avail_out === 0) {
        s.last_flush = -1;
        return Z_OK$3;
      }
    } else if (strm.avail_in === 0 && rank(flush) <= rank(old_flush) && flush !== Z_FINISH$3) {
      return err(strm, Z_BUF_ERROR$1);
    }
    if (s.status === FINISH_STATE2 && strm.avail_in !== 0) {
      return err(strm, Z_BUF_ERROR$1);
    }
    if (s.status === INIT_STATE2 && s.wrap === 0) {
      s.status = BUSY_STATE2;
    }
    if (s.status === INIT_STATE2) {
      let header = Z_DEFLATED$2 + (s.w_bits - 8 << 4) << 8;
      let level_flags = -1;
      if (s.strategy >= Z_HUFFMAN_ONLY2 || s.level < 2) {
        level_flags = 0;
      } else if (s.level < 6) {
        level_flags = 1;
      } else if (s.level === 6) {
        level_flags = 2;
      } else {
        level_flags = 3;
      }
      header |= level_flags << 6;
      if (s.strstart !== 0) {
        header |= PRESET_DICT3;
      }
      header += 31 - header % 31;
      putShortMSB(s, header);
      if (s.strstart !== 0) {
        putShortMSB(s, strm.adler >>> 16);
        putShortMSB(s, strm.adler & 65535);
      }
      strm.adler = 1;
      s.status = BUSY_STATE2;
      flush_pending(strm);
      if (s.pending !== 0) {
        s.last_flush = -1;
        return Z_OK$3;
      }
    }
    if (s.status === GZIP_STATE) {
      strm.adler = 0;
      put_byte(s, 31);
      put_byte(s, 139);
      put_byte(s, 8);
      if (!s.gzhead) {
        put_byte(s, 0);
        put_byte(s, 0);
        put_byte(s, 0);
        put_byte(s, 0);
        put_byte(s, 0);
        put_byte(s, s.level === 9 ? 2 : s.strategy >= Z_HUFFMAN_ONLY2 || s.level < 2 ? 4 : 0);
        put_byte(s, OS_CODE);
        s.status = BUSY_STATE2;
        flush_pending(strm);
        if (s.pending !== 0) {
          s.last_flush = -1;
          return Z_OK$3;
        }
      } else {
        put_byte(
          s,
          (s.gzhead.text ? 1 : 0) + (s.gzhead.hcrc ? 2 : 0) + (!s.gzhead.extra ? 0 : 4) + (!s.gzhead.name ? 0 : 8) + (!s.gzhead.comment ? 0 : 16)
        );
        put_byte(s, s.gzhead.time & 255);
        put_byte(s, s.gzhead.time >> 8 & 255);
        put_byte(s, s.gzhead.time >> 16 & 255);
        put_byte(s, s.gzhead.time >> 24 & 255);
        put_byte(s, s.level === 9 ? 2 : s.strategy >= Z_HUFFMAN_ONLY2 || s.level < 2 ? 4 : 0);
        put_byte(s, s.gzhead.os & 255);
        if (s.gzhead.extra && s.gzhead.extra.length) {
          put_byte(s, s.gzhead.extra.length & 255);
          put_byte(s, s.gzhead.extra.length >> 8 & 255);
        }
        if (s.gzhead.hcrc) {
          strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending, 0);
        }
        s.gzindex = 0;
        s.status = EXTRA_STATE;
      }
    }
    if (s.status === EXTRA_STATE) {
      if (s.gzhead.extra) {
        let beg = s.pending;
        let left = (s.gzhead.extra.length & 65535) - s.gzindex;
        while (s.pending + left > s.pending_buf_size) {
          let copy = s.pending_buf_size - s.pending;
          s.pending_buf.set(s.gzhead.extra.subarray(s.gzindex, s.gzindex + copy), s.pending);
          s.pending = s.pending_buf_size;
          if (s.gzhead.hcrc && s.pending > beg) {
            strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
          }
          s.gzindex += copy;
          flush_pending(strm);
          if (s.pending !== 0) {
            s.last_flush = -1;
            return Z_OK$3;
          }
          beg = 0;
          left -= copy;
        }
        let gzhead_extra = new Uint8Array(s.gzhead.extra);
        s.pending_buf.set(gzhead_extra.subarray(s.gzindex, s.gzindex + left), s.pending);
        s.pending += left;
        if (s.gzhead.hcrc && s.pending > beg) {
          strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
        }
        s.gzindex = 0;
      }
      s.status = NAME_STATE;
    }
    if (s.status === NAME_STATE) {
      if (s.gzhead.name) {
        let beg = s.pending;
        let val;
        do {
          if (s.pending === s.pending_buf_size) {
            if (s.gzhead.hcrc && s.pending > beg) {
              strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
            }
            flush_pending(strm);
            if (s.pending !== 0) {
              s.last_flush = -1;
              return Z_OK$3;
            }
            beg = 0;
          }
          if (s.gzindex < s.gzhead.name.length) {
            val = s.gzhead.name.charCodeAt(s.gzindex++) & 255;
          } else {
            val = 0;
          }
          put_byte(s, val);
        } while (val !== 0);
        if (s.gzhead.hcrc && s.pending > beg) {
          strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
        }
        s.gzindex = 0;
      }
      s.status = COMMENT_STATE;
    }
    if (s.status === COMMENT_STATE) {
      if (s.gzhead.comment) {
        let beg = s.pending;
        let val;
        do {
          if (s.pending === s.pending_buf_size) {
            if (s.gzhead.hcrc && s.pending > beg) {
              strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
            }
            flush_pending(strm);
            if (s.pending !== 0) {
              s.last_flush = -1;
              return Z_OK$3;
            }
            beg = 0;
          }
          if (s.gzindex < s.gzhead.comment.length) {
            val = s.gzhead.comment.charCodeAt(s.gzindex++) & 255;
          } else {
            val = 0;
          }
          put_byte(s, val);
        } while (val !== 0);
        if (s.gzhead.hcrc && s.pending > beg) {
          strm.adler = crc32_1(strm.adler, s.pending_buf, s.pending - beg, beg);
        }
      }
      s.status = HCRC_STATE;
    }
    if (s.status === HCRC_STATE) {
      if (s.gzhead.hcrc) {
        if (s.pending + 2 > s.pending_buf_size) {
          flush_pending(strm);
          if (s.pending !== 0) {
            s.last_flush = -1;
            return Z_OK$3;
          }
        }
        put_byte(s, strm.adler & 255);
        put_byte(s, strm.adler >> 8 & 255);
        strm.adler = 0;
      }
      s.status = BUSY_STATE2;
      flush_pending(strm);
      if (s.pending !== 0) {
        s.last_flush = -1;
        return Z_OK$3;
      }
    }
    if (strm.avail_in !== 0 || s.lookahead !== 0 || flush !== Z_NO_FLUSH$2 && s.status !== FINISH_STATE2) {
      let bstate = s.level === 0 ? deflate_stored(s, flush) : s.strategy === Z_HUFFMAN_ONLY2 ? deflate_huff(s, flush) : s.strategy === Z_RLE ? deflate_rle(s, flush) : configuration_table[s.level].func(s, flush);
      if (bstate === BS_FINISH_STARTED || bstate === BS_FINISH_DONE) {
        s.status = FINISH_STATE2;
      }
      if (bstate === BS_NEED_MORE || bstate === BS_FINISH_STARTED) {
        if (strm.avail_out === 0) {
          s.last_flush = -1;
        }
        return Z_OK$3;
      }
      if (bstate === BS_BLOCK_DONE) {
        if (flush === Z_PARTIAL_FLUSH2) {
          _tr_align(s);
        } else if (flush !== Z_BLOCK$1) {
          _tr_stored_block(s, 0, 0, false);
          if (flush === Z_FULL_FLUSH$1) {
            zero(s.head);
            if (s.lookahead === 0) {
              s.strstart = 0;
              s.block_start = 0;
              s.insert = 0;
            }
          }
        }
        flush_pending(strm);
        if (strm.avail_out === 0) {
          s.last_flush = -1;
          return Z_OK$3;
        }
      }
    }
    if (flush !== Z_FINISH$3) {
      return Z_OK$3;
    }
    if (s.wrap <= 0) {
      return Z_STREAM_END$3;
    }
    if (s.wrap === 2) {
      put_byte(s, strm.adler & 255);
      put_byte(s, strm.adler >> 8 & 255);
      put_byte(s, strm.adler >> 16 & 255);
      put_byte(s, strm.adler >> 24 & 255);
      put_byte(s, strm.total_in & 255);
      put_byte(s, strm.total_in >> 8 & 255);
      put_byte(s, strm.total_in >> 16 & 255);
      put_byte(s, strm.total_in >> 24 & 255);
    } else {
      putShortMSB(s, strm.adler >>> 16);
      putShortMSB(s, strm.adler & 65535);
    }
    flush_pending(strm);
    if (s.wrap > 0) {
      s.wrap = -s.wrap;
    }
    return s.pending !== 0 ? Z_OK$3 : Z_STREAM_END$3;
  };
  var deflateEnd = (strm) => {
    if (deflateStateCheck(strm)) {
      return Z_STREAM_ERROR$2;
    }
    const status = strm.state.status;
    strm.state = null;
    return status === BUSY_STATE2 ? err(strm, Z_DATA_ERROR$2) : Z_OK$3;
  };
  var deflateSetDictionary = (strm, dictionary) => {
    let dictLength = dictionary.length;
    if (deflateStateCheck(strm)) {
      return Z_STREAM_ERROR$2;
    }
    const s = strm.state;
    const wrap = s.wrap;
    if (wrap === 2 || wrap === 1 && s.status !== INIT_STATE2 || s.lookahead) {
      return Z_STREAM_ERROR$2;
    }
    if (wrap === 1) {
      strm.adler = adler32_1(strm.adler, dictionary, dictLength, 0);
    }
    s.wrap = 0;
    if (dictLength >= s.w_size) {
      if (wrap === 0) {
        zero(s.head);
        s.strstart = 0;
        s.block_start = 0;
        s.insert = 0;
      }
      let tmpDict = new Uint8Array(s.w_size);
      tmpDict.set(dictionary.subarray(dictLength - s.w_size, dictLength), 0);
      dictionary = tmpDict;
      dictLength = s.w_size;
    }
    const avail = strm.avail_in;
    const next = strm.next_in;
    const input = strm.input;
    strm.avail_in = dictLength;
    strm.next_in = 0;
    strm.input = dictionary;
    fill_window(s);
    while (s.lookahead >= MIN_MATCH2) {
      let str = s.strstart;
      let n = s.lookahead - (MIN_MATCH2 - 1);
      do {
        s.ins_h = HASH(s, s.ins_h, s.window[str + MIN_MATCH2 - 1]);
        s.prev[str & s.w_mask] = s.head[s.ins_h];
        s.head[s.ins_h] = str;
        str++;
      } while (--n);
      s.strstart = str;
      s.lookahead = MIN_MATCH2 - 1;
      fill_window(s);
    }
    s.strstart += s.lookahead;
    s.block_start = s.strstart;
    s.insert = s.lookahead;
    s.lookahead = 0;
    s.match_length = s.prev_length = MIN_MATCH2 - 1;
    s.match_available = 0;
    strm.next_in = next;
    strm.input = input;
    strm.avail_in = avail;
    s.wrap = wrap;
    return Z_OK$3;
  };
  var deflateInit_1 = deflateInit;
  var deflateInit2_1 = deflateInit2;
  var deflateReset_1 = deflateReset;
  var deflateResetKeep_1 = deflateResetKeep;
  var deflateSetHeader_1 = deflateSetHeader;
  var deflate_2$1 = deflate$2;
  var deflateEnd_1 = deflateEnd;
  var deflateSetDictionary_1 = deflateSetDictionary;
  var deflateInfo = "pako deflate (from Nodeca project)";
  var deflate_1$2 = {
    deflateInit: deflateInit_1,
    deflateInit2: deflateInit2_1,
    deflateReset: deflateReset_1,
    deflateResetKeep: deflateResetKeep_1,
    deflateSetHeader: deflateSetHeader_1,
    deflate: deflate_2$1,
    deflateEnd: deflateEnd_1,
    deflateSetDictionary: deflateSetDictionary_1,
    deflateInfo
  };
  var _has = (obj, key) => {
    return Object.prototype.hasOwnProperty.call(obj, key);
  };
  var assign = function(obj) {
    const sources = Array.prototype.slice.call(arguments, 1);
    while (sources.length) {
      const source = sources.shift();
      if (!source) {
        continue;
      }
      if (typeof source !== "object") {
        throw new TypeError(source + "must be non-object");
      }
      for (const p in source) {
        if (_has(source, p)) {
          obj[p] = source[p];
        }
      }
    }
    return obj;
  };
  var flattenChunks = (chunks) => {
    let len = 0;
    for (let i = 0, l = chunks.length; i < l; i++) {
      len += chunks[i].length;
    }
    const result = new Uint8Array(len);
    for (let i = 0, pos = 0, l = chunks.length; i < l; i++) {
      let chunk = chunks[i];
      result.set(chunk, pos);
      pos += chunk.length;
    }
    return result;
  };
  var common = {
    assign,
    flattenChunks
  };
  var STR_APPLY_UIA_OK = true;
  try {
    String.fromCharCode.apply(null, new Uint8Array(1));
  } catch (__) {
    STR_APPLY_UIA_OK = false;
  }
  var _utf8len = new Uint8Array(256);
  for (let q = 0; q < 256; q++) {
    _utf8len[q] = q >= 252 ? 6 : q >= 248 ? 5 : q >= 240 ? 4 : q >= 224 ? 3 : q >= 192 ? 2 : 1;
  }
  _utf8len[254] = _utf8len[254] = 1;
  var string2buf = (str) => {
    if (typeof TextEncoder === "function" && TextEncoder.prototype.encode) {
      return new TextEncoder().encode(str);
    }
    let buf, c, c2, m_pos, i, str_len = str.length, buf_len = 0;
    for (m_pos = 0; m_pos < str_len; m_pos++) {
      c = str.charCodeAt(m_pos);
      if ((c & 64512) === 55296 && m_pos + 1 < str_len) {
        c2 = str.charCodeAt(m_pos + 1);
        if ((c2 & 64512) === 56320) {
          c = 65536 + (c - 55296 << 10) + (c2 - 56320);
          m_pos++;
        }
      }
      buf_len += c < 128 ? 1 : c < 2048 ? 2 : c < 65536 ? 3 : 4;
    }
    buf = new Uint8Array(buf_len);
    for (i = 0, m_pos = 0; i < buf_len; m_pos++) {
      c = str.charCodeAt(m_pos);
      if ((c & 64512) === 55296 && m_pos + 1 < str_len) {
        c2 = str.charCodeAt(m_pos + 1);
        if ((c2 & 64512) === 56320) {
          c = 65536 + (c - 55296 << 10) + (c2 - 56320);
          m_pos++;
        }
      }
      if (c < 128) {
        buf[i++] = c;
      } else if (c < 2048) {
        buf[i++] = 192 | c >>> 6;
        buf[i++] = 128 | c & 63;
      } else if (c < 65536) {
        buf[i++] = 224 | c >>> 12;
        buf[i++] = 128 | c >>> 6 & 63;
        buf[i++] = 128 | c & 63;
      } else {
        buf[i++] = 240 | c >>> 18;
        buf[i++] = 128 | c >>> 12 & 63;
        buf[i++] = 128 | c >>> 6 & 63;
        buf[i++] = 128 | c & 63;
      }
    }
    return buf;
  };
  var buf2binstring = (buf, len) => {
    if (len < 65534) {
      if (buf.subarray && STR_APPLY_UIA_OK) {
        return String.fromCharCode.apply(null, buf.length === len ? buf : buf.subarray(0, len));
      }
    }
    let result = "";
    for (let i = 0; i < len; i++) {
      result += String.fromCharCode(buf[i]);
    }
    return result;
  };
  var buf2string = (buf, max) => {
    const len = max || buf.length;
    if (typeof TextDecoder === "function" && TextDecoder.prototype.decode) {
      return new TextDecoder().decode(buf.subarray(0, max));
    }
    let i, out;
    const utf16buf = new Array(len * 2);
    for (out = 0, i = 0; i < len; ) {
      let c = buf[i++];
      if (c < 128) {
        utf16buf[out++] = c;
        continue;
      }
      let c_len = _utf8len[c];
      if (c_len > 4) {
        utf16buf[out++] = 65533;
        i += c_len - 1;
        continue;
      }
      c &= c_len === 2 ? 31 : c_len === 3 ? 15 : 7;
      while (c_len > 1 && i < len) {
        c = c << 6 | buf[i++] & 63;
        c_len--;
      }
      if (c_len > 1) {
        utf16buf[out++] = 65533;
        continue;
      }
      if (c < 65536) {
        utf16buf[out++] = c;
      } else {
        c -= 65536;
        utf16buf[out++] = 55296 | c >> 10 & 1023;
        utf16buf[out++] = 56320 | c & 1023;
      }
    }
    return buf2binstring(utf16buf, out);
  };
  var utf8border = (buf, max) => {
    max = max || buf.length;
    if (max > buf.length) {
      max = buf.length;
    }
    let pos = max - 1;
    while (pos >= 0 && (buf[pos] & 192) === 128) {
      pos--;
    }
    if (pos < 0) {
      return max;
    }
    if (pos === 0) {
      return max;
    }
    return pos + _utf8len[buf[pos]] > max ? pos : max;
  };
  var strings = {
    string2buf,
    buf2string,
    utf8border
  };
  function ZStream3() {
    this.input = null;
    this.next_in = 0;
    this.avail_in = 0;
    this.total_in = 0;
    this.output = null;
    this.next_out = 0;
    this.avail_out = 0;
    this.total_out = 0;
    this.msg = "";
    this.state = null;
    this.data_type = 2;
    this.adler = 0;
  }
  var zstream = ZStream3;
  var toString$1 = Object.prototype.toString;
  var {
    Z_NO_FLUSH: Z_NO_FLUSH$1,
    Z_SYNC_FLUSH,
    Z_FULL_FLUSH: Z_FULL_FLUSH2,
    Z_FINISH: Z_FINISH$2,
    Z_OK: Z_OK$2,
    Z_STREAM_END: Z_STREAM_END$2,
    Z_DEFAULT_COMPRESSION: Z_DEFAULT_COMPRESSION2,
    Z_DEFAULT_STRATEGY: Z_DEFAULT_STRATEGY2,
    Z_DEFLATED: Z_DEFLATED$1
  } = constants$2;
  function Deflate$1(options) {
    this.options = common.assign({
      level: Z_DEFAULT_COMPRESSION2,
      method: Z_DEFLATED$1,
      chunkSize: 16384,
      windowBits: 15,
      memLevel: 8,
      strategy: Z_DEFAULT_STRATEGY2
    }, options || {});
    let opt = this.options;
    if (opt.raw && opt.windowBits > 0) {
      opt.windowBits = -opt.windowBits;
    } else if (opt.gzip && opt.windowBits > 0 && opt.windowBits < 16) {
      opt.windowBits += 16;
    }
    this.err = 0;
    this.msg = "";
    this.ended = false;
    this.chunks = [];
    this.strm = new zstream();
    this.strm.avail_out = 0;
    let status = deflate_1$2.deflateInit2(
      this.strm,
      opt.level,
      opt.method,
      opt.windowBits,
      opt.memLevel,
      opt.strategy
    );
    if (status !== Z_OK$2) {
      throw new Error(messages[status]);
    }
    if (opt.header) {
      deflate_1$2.deflateSetHeader(this.strm, opt.header);
    }
    if (opt.dictionary) {
      let dict;
      if (typeof opt.dictionary === "string") {
        dict = strings.string2buf(opt.dictionary);
      } else if (toString$1.call(opt.dictionary) === "[object ArrayBuffer]") {
        dict = new Uint8Array(opt.dictionary);
      } else {
        dict = opt.dictionary;
      }
      status = deflate_1$2.deflateSetDictionary(this.strm, dict);
      if (status !== Z_OK$2) {
        throw new Error(messages[status]);
      }
      this._dict_set = true;
    }
  }
  Deflate$1.prototype.push = function(data, flush_mode) {
    const strm = this.strm;
    const chunkSize = this.options.chunkSize;
    let status, _flush_mode;
    if (this.ended) {
      return false;
    }
    if (flush_mode === ~~flush_mode) _flush_mode = flush_mode;
    else _flush_mode = flush_mode === true ? Z_FINISH$2 : Z_NO_FLUSH$1;
    if (typeof data === "string") {
      strm.input = strings.string2buf(data);
    } else if (toString$1.call(data) === "[object ArrayBuffer]") {
      strm.input = new Uint8Array(data);
    } else {
      strm.input = data;
    }
    strm.next_in = 0;
    strm.avail_in = strm.input.length;
    for (; ; ) {
      if (strm.avail_out === 0) {
        strm.output = new Uint8Array(chunkSize);
        strm.next_out = 0;
        strm.avail_out = chunkSize;
      }
      if ((_flush_mode === Z_SYNC_FLUSH || _flush_mode === Z_FULL_FLUSH2) && strm.avail_out <= 6) {
        this.onData(strm.output.subarray(0, strm.next_out));
        strm.avail_out = 0;
        continue;
      }
      status = deflate_1$2.deflate(strm, _flush_mode);
      if (status === Z_STREAM_END$2) {
        if (strm.next_out > 0) {
          this.onData(strm.output.subarray(0, strm.next_out));
        }
        status = deflate_1$2.deflateEnd(this.strm);
        this.onEnd(status);
        this.ended = true;
        return status === Z_OK$2;
      }
      if (strm.avail_out === 0) {
        this.onData(strm.output);
        continue;
      }
      if (_flush_mode > 0 && strm.next_out > 0) {
        this.onData(strm.output.subarray(0, strm.next_out));
        strm.avail_out = 0;
        continue;
      }
      if (strm.avail_in === 0) break;
    }
    return true;
  };
  Deflate$1.prototype.onData = function(chunk) {
    this.chunks.push(chunk);
  };
  Deflate$1.prototype.onEnd = function(status) {
    if (status === Z_OK$2) {
      this.result = common.flattenChunks(this.chunks);
    }
    this.chunks = [];
    this.err = status;
    this.msg = this.strm.msg;
  };
  function deflate$1(input, options) {
    const deflator = new Deflate$1(options);
    deflator.push(input, true);
    if (deflator.err) {
      throw deflator.msg || messages[deflator.err];
    }
    return deflator.result;
  }
  function deflateRaw$1(input, options) {
    options = options || {};
    options.raw = true;
    return deflate$1(input, options);
  }
  function gzip$1(input, options) {
    options = options || {};
    options.gzip = true;
    return deflate$1(input, options);
  }
  var Deflate_1$1 = Deflate$1;
  var deflate_2 = deflate$1;
  var deflateRaw_1$1 = deflateRaw$1;
  var gzip_1$1 = gzip$1;
  var constants$1 = constants$2;
  var deflate_1$1 = {
    Deflate: Deflate_1$1,
    deflate: deflate_2,
    deflateRaw: deflateRaw_1$1,
    gzip: gzip_1$1,
    constants: constants$1
  };
  var BAD$1 = 16209;
  var TYPE$1 = 16191;
  var inffast = function inflate_fast(strm, start) {
    let _in;
    let last;
    let _out;
    let beg;
    let end;
    let dmax;
    let wsize;
    let whave;
    let wnext;
    let s_window;
    let hold;
    let bits;
    let lcode;
    let dcode;
    let lmask;
    let dmask;
    let here;
    let op;
    let len;
    let dist;
    let from;
    let from_source;
    let input, output;
    const state = strm.state;
    _in = strm.next_in;
    input = strm.input;
    last = _in + (strm.avail_in - 5);
    _out = strm.next_out;
    output = strm.output;
    beg = _out - (start - strm.avail_out);
    end = _out + (strm.avail_out - 257);
    dmax = state.dmax;
    wsize = state.wsize;
    whave = state.whave;
    wnext = state.wnext;
    s_window = state.window;
    hold = state.hold;
    bits = state.bits;
    lcode = state.lencode;
    dcode = state.distcode;
    lmask = (1 << state.lenbits) - 1;
    dmask = (1 << state.distbits) - 1;
    top:
      do {
        if (bits < 15) {
          hold += input[_in++] << bits;
          bits += 8;
          hold += input[_in++] << bits;
          bits += 8;
        }
        here = lcode[hold & lmask];
        dolen:
          for (; ; ) {
            op = here >>> 24;
            hold >>>= op;
            bits -= op;
            op = here >>> 16 & 255;
            if (op === 0) {
              output[_out++] = here & 65535;
            } else if (op & 16) {
              len = here & 65535;
              op &= 15;
              if (op) {
                if (bits < op) {
                  hold += input[_in++] << bits;
                  bits += 8;
                }
                len += hold & (1 << op) - 1;
                hold >>>= op;
                bits -= op;
              }
              if (bits < 15) {
                hold += input[_in++] << bits;
                bits += 8;
                hold += input[_in++] << bits;
                bits += 8;
              }
              here = dcode[hold & dmask];
              dodist:
                for (; ; ) {
                  op = here >>> 24;
                  hold >>>= op;
                  bits -= op;
                  op = here >>> 16 & 255;
                  if (op & 16) {
                    dist = here & 65535;
                    op &= 15;
                    if (bits < op) {
                      hold += input[_in++] << bits;
                      bits += 8;
                      if (bits < op) {
                        hold += input[_in++] << bits;
                        bits += 8;
                      }
                    }
                    dist += hold & (1 << op) - 1;
                    if (dist > dmax) {
                      strm.msg = "invalid distance too far back";
                      state.mode = BAD$1;
                      break top;
                    }
                    hold >>>= op;
                    bits -= op;
                    op = _out - beg;
                    if (dist > op) {
                      op = dist - op;
                      if (op > whave) {
                        if (state.sane) {
                          strm.msg = "invalid distance too far back";
                          state.mode = BAD$1;
                          break top;
                        }
                      }
                      from = 0;
                      from_source = s_window;
                      if (wnext === 0) {
                        from += wsize - op;
                        if (op < len) {
                          len -= op;
                          do {
                            output[_out++] = s_window[from++];
                          } while (--op);
                          from = _out - dist;
                          from_source = output;
                        }
                      } else if (wnext < op) {
                        from += wsize + wnext - op;
                        op -= wnext;
                        if (op < len) {
                          len -= op;
                          do {
                            output[_out++] = s_window[from++];
                          } while (--op);
                          from = 0;
                          if (wnext < len) {
                            op = wnext;
                            len -= op;
                            do {
                              output[_out++] = s_window[from++];
                            } while (--op);
                            from = _out - dist;
                            from_source = output;
                          }
                        }
                      } else {
                        from += wnext - op;
                        if (op < len) {
                          len -= op;
                          do {
                            output[_out++] = s_window[from++];
                          } while (--op);
                          from = _out - dist;
                          from_source = output;
                        }
                      }
                      while (len > 2) {
                        output[_out++] = from_source[from++];
                        output[_out++] = from_source[from++];
                        output[_out++] = from_source[from++];
                        len -= 3;
                      }
                      if (len) {
                        output[_out++] = from_source[from++];
                        if (len > 1) {
                          output[_out++] = from_source[from++];
                        }
                      }
                    } else {
                      from = _out - dist;
                      do {
                        output[_out++] = output[from++];
                        output[_out++] = output[from++];
                        output[_out++] = output[from++];
                        len -= 3;
                      } while (len > 2);
                      if (len) {
                        output[_out++] = output[from++];
                        if (len > 1) {
                          output[_out++] = output[from++];
                        }
                      }
                    }
                  } else if ((op & 64) === 0) {
                    here = dcode[(here & 65535) + (hold & (1 << op) - 1)];
                    continue dodist;
                  } else {
                    strm.msg = "invalid distance code";
                    state.mode = BAD$1;
                    break top;
                  }
                  break;
                }
            } else if ((op & 64) === 0) {
              here = lcode[(here & 65535) + (hold & (1 << op) - 1)];
              continue dolen;
            } else if (op & 32) {
              state.mode = TYPE$1;
              break top;
            } else {
              strm.msg = "invalid literal/length code";
              state.mode = BAD$1;
              break top;
            }
            break;
          }
      } while (_in < last && _out < end);
    len = bits >> 3;
    _in -= len;
    bits -= len << 3;
    hold &= (1 << bits) - 1;
    strm.next_in = _in;
    strm.next_out = _out;
    strm.avail_in = _in < last ? 5 + (last - _in) : 5 - (_in - last);
    strm.avail_out = _out < end ? 257 + (end - _out) : 257 - (_out - end);
    state.hold = hold;
    state.bits = bits;
    return;
  };
  var MAXBITS = 15;
  var ENOUGH_LENS$1 = 852;
  var ENOUGH_DISTS$1 = 592;
  var CODES$1 = 0;
  var LENS$1 = 1;
  var DISTS$1 = 2;
  var lbase = new Uint16Array([
    /* Length codes 257..285 base */
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    13,
    15,
    17,
    19,
    23,
    27,
    31,
    35,
    43,
    51,
    59,
    67,
    83,
    99,
    115,
    131,
    163,
    195,
    227,
    258,
    0,
    0
  ]);
  var lext = new Uint8Array([
    /* Length codes 257..285 extra */
    16,
    16,
    16,
    16,
    16,
    16,
    16,
    16,
    17,
    17,
    17,
    17,
    18,
    18,
    18,
    18,
    19,
    19,
    19,
    19,
    20,
    20,
    20,
    20,
    21,
    21,
    21,
    21,
    16,
    72,
    78
  ]);
  var dbase = new Uint16Array([
    /* Distance codes 0..29 base */
    1,
    2,
    3,
    4,
    5,
    7,
    9,
    13,
    17,
    25,
    33,
    49,
    65,
    97,
    129,
    193,
    257,
    385,
    513,
    769,
    1025,
    1537,
    2049,
    3073,
    4097,
    6145,
    8193,
    12289,
    16385,
    24577,
    0,
    0
  ]);
  var dext = new Uint8Array([
    /* Distance codes 0..29 extra */
    16,
    16,
    16,
    16,
    17,
    17,
    18,
    18,
    19,
    19,
    20,
    20,
    21,
    21,
    22,
    22,
    23,
    23,
    24,
    24,
    25,
    25,
    26,
    26,
    27,
    27,
    28,
    28,
    29,
    29,
    64,
    64
  ]);
  var inflate_table = (type, lens, lens_index, codes, table3, table_index, work, opts) => {
    const bits = opts.bits;
    let len = 0;
    let sym = 0;
    let min = 0, max = 0;
    let root = 0;
    let curr = 0;
    let drop = 0;
    let left = 0;
    let used = 0;
    let huff = 0;
    let incr;
    let fill;
    let low;
    let mask;
    let next;
    let base = null;
    let match;
    const count = new Uint16Array(MAXBITS + 1);
    const offs = new Uint16Array(MAXBITS + 1);
    let extra = null;
    let here_bits, here_op, here_val;
    for (len = 0; len <= MAXBITS; len++) {
      count[len] = 0;
    }
    for (sym = 0; sym < codes; sym++) {
      count[lens[lens_index + sym]]++;
    }
    root = bits;
    for (max = MAXBITS; max >= 1; max--) {
      if (count[max] !== 0) {
        break;
      }
    }
    if (root > max) {
      root = max;
    }
    if (max === 0) {
      table3[table_index++] = 1 << 24 | 64 << 16 | 0;
      table3[table_index++] = 1 << 24 | 64 << 16 | 0;
      opts.bits = 1;
      return 0;
    }
    for (min = 1; min < max; min++) {
      if (count[min] !== 0) {
        break;
      }
    }
    if (root < min) {
      root = min;
    }
    left = 1;
    for (len = 1; len <= MAXBITS; len++) {
      left <<= 1;
      left -= count[len];
      if (left < 0) {
        return -1;
      }
    }
    if (left > 0 && (type === CODES$1 || max !== 1)) {
      return -1;
    }
    offs[1] = 0;
    for (len = 1; len < MAXBITS; len++) {
      offs[len + 1] = offs[len] + count[len];
    }
    for (sym = 0; sym < codes; sym++) {
      if (lens[lens_index + sym] !== 0) {
        work[offs[lens[lens_index + sym]]++] = sym;
      }
    }
    if (type === CODES$1) {
      base = extra = work;
      match = 20;
    } else if (type === LENS$1) {
      base = lbase;
      extra = lext;
      match = 257;
    } else {
      base = dbase;
      extra = dext;
      match = 0;
    }
    huff = 0;
    sym = 0;
    len = min;
    next = table_index;
    curr = root;
    drop = 0;
    low = -1;
    used = 1 << root;
    mask = used - 1;
    if (type === LENS$1 && used > ENOUGH_LENS$1 || type === DISTS$1 && used > ENOUGH_DISTS$1) {
      return 1;
    }
    for (; ; ) {
      here_bits = len - drop;
      if (work[sym] + 1 < match) {
        here_op = 0;
        here_val = work[sym];
      } else if (work[sym] >= match) {
        here_op = extra[work[sym] - match];
        here_val = base[work[sym] - match];
      } else {
        here_op = 32 + 64;
        here_val = 0;
      }
      incr = 1 << len - drop;
      fill = 1 << curr;
      min = fill;
      do {
        fill -= incr;
        table3[next + (huff >> drop) + fill] = here_bits << 24 | here_op << 16 | here_val | 0;
      } while (fill !== 0);
      incr = 1 << len - 1;
      while (huff & incr) {
        incr >>= 1;
      }
      if (incr !== 0) {
        huff &= incr - 1;
        huff += incr;
      } else {
        huff = 0;
      }
      sym++;
      if (--count[len] === 0) {
        if (len === max) {
          break;
        }
        len = lens[lens_index + work[sym]];
      }
      if (len > root && (huff & mask) !== low) {
        if (drop === 0) {
          drop = root;
        }
        next += min;
        curr = len - drop;
        left = 1 << curr;
        while (curr + drop < max) {
          left -= count[curr + drop];
          if (left <= 0) {
            break;
          }
          curr++;
          left <<= 1;
        }
        used += 1 << curr;
        if (type === LENS$1 && used > ENOUGH_LENS$1 || type === DISTS$1 && used > ENOUGH_DISTS$1) {
          return 1;
        }
        low = huff & mask;
        table3[low] = root << 24 | curr << 16 | next - table_index | 0;
      }
    }
    if (huff !== 0) {
      table3[next + huff] = len - drop << 24 | 64 << 16 | 0;
    }
    opts.bits = root;
    return 0;
  };
  var inftrees = inflate_table;
  var CODES2 = 0;
  var LENS2 = 1;
  var DISTS = 2;
  var {
    Z_FINISH: Z_FINISH$1,
    Z_BLOCK,
    Z_TREES,
    Z_OK: Z_OK$1,
    Z_STREAM_END: Z_STREAM_END$1,
    Z_NEED_DICT: Z_NEED_DICT$1,
    Z_STREAM_ERROR: Z_STREAM_ERROR$1,
    Z_DATA_ERROR: Z_DATA_ERROR$1,
    Z_MEM_ERROR: Z_MEM_ERROR$1,
    Z_BUF_ERROR: Z_BUF_ERROR3,
    Z_DEFLATED: Z_DEFLATED3
  } = constants$2;
  var HEAD = 16180;
  var FLAGS = 16181;
  var TIME = 16182;
  var OS = 16183;
  var EXLEN = 16184;
  var EXTRA = 16185;
  var NAME = 16186;
  var COMMENT = 16187;
  var HCRC = 16188;
  var DICTID = 16189;
  var DICT = 16190;
  var TYPE2 = 16191;
  var TYPEDO = 16192;
  var STORED3 = 16193;
  var COPY_ = 16194;
  var COPY2 = 16195;
  var TABLE2 = 16196;
  var LENLENS = 16197;
  var CODELENS = 16198;
  var LEN_ = 16199;
  var LEN2 = 16200;
  var LENEXT2 = 16201;
  var DIST2 = 16202;
  var DISTEXT2 = 16203;
  var MATCH = 16204;
  var LIT2 = 16205;
  var CHECK = 16206;
  var LENGTH = 16207;
  var DONE2 = 16208;
  var BAD2 = 16209;
  var MEM = 16210;
  var SYNC = 16211;
  var ENOUGH_LENS = 852;
  var ENOUGH_DISTS = 592;
  var MAX_WBITS = 15;
  var DEF_WBITS = MAX_WBITS;
  var zswap32 = (q) => {
    return (q >>> 24 & 255) + (q >>> 8 & 65280) + ((q & 65280) << 8) + ((q & 255) << 24);
  };
  function InflateState() {
    this.strm = null;
    this.mode = 0;
    this.last = false;
    this.wrap = 0;
    this.havedict = false;
    this.flags = 0;
    this.dmax = 0;
    this.check = 0;
    this.total = 0;
    this.head = null;
    this.wbits = 0;
    this.wsize = 0;
    this.whave = 0;
    this.wnext = 0;
    this.window = null;
    this.hold = 0;
    this.bits = 0;
    this.length = 0;
    this.offset = 0;
    this.extra = 0;
    this.lencode = null;
    this.distcode = null;
    this.lenbits = 0;
    this.distbits = 0;
    this.ncode = 0;
    this.nlen = 0;
    this.ndist = 0;
    this.have = 0;
    this.next = null;
    this.lens = new Uint16Array(320);
    this.work = new Uint16Array(288);
    this.lendyn = null;
    this.distdyn = null;
    this.sane = 0;
    this.back = 0;
    this.was = 0;
  }
  var inflateStateCheck = (strm) => {
    if (!strm) {
      return 1;
    }
    const state = strm.state;
    if (!state || state.strm !== strm || state.mode < HEAD || state.mode > SYNC) {
      return 1;
    }
    return 0;
  };
  var inflateResetKeep = (strm) => {
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    const state = strm.state;
    strm.total_in = strm.total_out = state.total = 0;
    strm.msg = "";
    if (state.wrap) {
      strm.adler = state.wrap & 1;
    }
    state.mode = HEAD;
    state.last = 0;
    state.havedict = 0;
    state.flags = -1;
    state.dmax = 32768;
    state.head = null;
    state.hold = 0;
    state.bits = 0;
    state.lencode = state.lendyn = new Int32Array(ENOUGH_LENS);
    state.distcode = state.distdyn = new Int32Array(ENOUGH_DISTS);
    state.sane = 1;
    state.back = -1;
    return Z_OK$1;
  };
  var inflateReset = (strm) => {
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    const state = strm.state;
    state.wsize = 0;
    state.whave = 0;
    state.wnext = 0;
    return inflateResetKeep(strm);
  };
  var inflateReset2 = (strm, windowBits) => {
    let wrap;
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    const state = strm.state;
    if (windowBits < 0) {
      wrap = 0;
      windowBits = -windowBits;
    } else {
      wrap = (windowBits >> 4) + 5;
      if (windowBits < 48) {
        windowBits &= 15;
      }
    }
    if (windowBits && (windowBits < 8 || windowBits > 15)) {
      return Z_STREAM_ERROR$1;
    }
    if (state.window !== null && state.wbits !== windowBits) {
      state.window = null;
    }
    state.wrap = wrap;
    state.wbits = windowBits;
    return inflateReset(strm);
  };
  var inflateInit2 = (strm, windowBits) => {
    if (!strm) {
      return Z_STREAM_ERROR$1;
    }
    const state = new InflateState();
    strm.state = state;
    state.strm = strm;
    state.window = null;
    state.mode = HEAD;
    const ret = inflateReset2(strm, windowBits);
    if (ret !== Z_OK$1) {
      strm.state = null;
    }
    return ret;
  };
  var inflateInit = (strm) => {
    return inflateInit2(strm, DEF_WBITS);
  };
  var virgin = true;
  var lenfix;
  var distfix;
  var fixedtables = (state) => {
    if (virgin) {
      lenfix = new Int32Array(512);
      distfix = new Int32Array(32);
      let sym = 0;
      while (sym < 144) {
        state.lens[sym++] = 8;
      }
      while (sym < 256) {
        state.lens[sym++] = 9;
      }
      while (sym < 280) {
        state.lens[sym++] = 7;
      }
      while (sym < 288) {
        state.lens[sym++] = 8;
      }
      inftrees(LENS2, state.lens, 0, 288, lenfix, 0, state.work, { bits: 9 });
      sym = 0;
      while (sym < 32) {
        state.lens[sym++] = 5;
      }
      inftrees(DISTS, state.lens, 0, 32, distfix, 0, state.work, { bits: 5 });
      virgin = false;
    }
    state.lencode = lenfix;
    state.lenbits = 9;
    state.distcode = distfix;
    state.distbits = 5;
  };
  var updatewindow = (strm, src, end, copy) => {
    let dist;
    const state = strm.state;
    if (state.window === null) {
      state.wsize = 1 << state.wbits;
      state.wnext = 0;
      state.whave = 0;
      state.window = new Uint8Array(state.wsize);
    }
    if (copy >= state.wsize) {
      state.window.set(src.subarray(end - state.wsize, end), 0);
      state.wnext = 0;
      state.whave = state.wsize;
    } else {
      dist = state.wsize - state.wnext;
      if (dist > copy) {
        dist = copy;
      }
      state.window.set(src.subarray(end - copy, end - copy + dist), state.wnext);
      copy -= dist;
      if (copy) {
        state.window.set(src.subarray(end - copy, end), 0);
        state.wnext = copy;
        state.whave = state.wsize;
      } else {
        state.wnext += dist;
        if (state.wnext === state.wsize) {
          state.wnext = 0;
        }
        if (state.whave < state.wsize) {
          state.whave += dist;
        }
      }
    }
    return 0;
  };
  var inflate$2 = (strm, flush) => {
    let state;
    let input, output;
    let next;
    let put;
    let have, left;
    let hold;
    let bits;
    let _in, _out;
    let copy;
    let from;
    let from_source;
    let here = 0;
    let here_bits, here_op, here_val;
    let last_bits, last_op, last_val;
    let len;
    let ret;
    const hbuf = new Uint8Array(4);
    let opts;
    let n;
    const order = (
      /* permutation of code lengths */
      new Uint8Array([16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15])
    );
    if (inflateStateCheck(strm) || !strm.output || !strm.input && strm.avail_in !== 0) {
      return Z_STREAM_ERROR$1;
    }
    state = strm.state;
    if (state.mode === TYPE2) {
      state.mode = TYPEDO;
    }
    put = strm.next_out;
    output = strm.output;
    left = strm.avail_out;
    next = strm.next_in;
    input = strm.input;
    have = strm.avail_in;
    hold = state.hold;
    bits = state.bits;
    _in = have;
    _out = left;
    ret = Z_OK$1;
    inf_leave:
      for (; ; ) {
        switch (state.mode) {
          case HEAD:
            if (state.wrap === 0) {
              state.mode = TYPEDO;
              break;
            }
            while (bits < 16) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if (state.wrap & 2 && hold === 35615) {
              if (state.wbits === 0) {
                state.wbits = 15;
              }
              state.check = 0;
              hbuf[0] = hold & 255;
              hbuf[1] = hold >>> 8 & 255;
              state.check = crc32_1(state.check, hbuf, 2, 0);
              hold = 0;
              bits = 0;
              state.mode = FLAGS;
              break;
            }
            if (state.head) {
              state.head.done = false;
            }
            if (!(state.wrap & 1) || /* check if zlib header allowed */
            (((hold & 255) << 8) + (hold >> 8)) % 31) {
              strm.msg = "incorrect header check";
              state.mode = BAD2;
              break;
            }
            if ((hold & 15) !== Z_DEFLATED3) {
              strm.msg = "unknown compression method";
              state.mode = BAD2;
              break;
            }
            hold >>>= 4;
            bits -= 4;
            len = (hold & 15) + 8;
            if (state.wbits === 0) {
              state.wbits = len;
            }
            if (len > 15 || len > state.wbits) {
              strm.msg = "invalid window size";
              state.mode = BAD2;
              break;
            }
            state.dmax = 1 << state.wbits;
            state.flags = 0;
            strm.adler = state.check = 1;
            state.mode = hold & 512 ? DICTID : TYPE2;
            hold = 0;
            bits = 0;
            break;
          case FLAGS:
            while (bits < 16) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            state.flags = hold;
            if ((state.flags & 255) !== Z_DEFLATED3) {
              strm.msg = "unknown compression method";
              state.mode = BAD2;
              break;
            }
            if (state.flags & 57344) {
              strm.msg = "unknown header flags set";
              state.mode = BAD2;
              break;
            }
            if (state.head) {
              state.head.text = hold >> 8 & 1;
            }
            if (state.flags & 512 && state.wrap & 4) {
              hbuf[0] = hold & 255;
              hbuf[1] = hold >>> 8 & 255;
              state.check = crc32_1(state.check, hbuf, 2, 0);
            }
            hold = 0;
            bits = 0;
            state.mode = TIME;
          /* falls through */
          case TIME:
            while (bits < 32) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if (state.head) {
              state.head.time = hold;
            }
            if (state.flags & 512 && state.wrap & 4) {
              hbuf[0] = hold & 255;
              hbuf[1] = hold >>> 8 & 255;
              hbuf[2] = hold >>> 16 & 255;
              hbuf[3] = hold >>> 24 & 255;
              state.check = crc32_1(state.check, hbuf, 4, 0);
            }
            hold = 0;
            bits = 0;
            state.mode = OS;
          /* falls through */
          case OS:
            while (bits < 16) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if (state.head) {
              state.head.xflags = hold & 255;
              state.head.os = hold >> 8;
            }
            if (state.flags & 512 && state.wrap & 4) {
              hbuf[0] = hold & 255;
              hbuf[1] = hold >>> 8 & 255;
              state.check = crc32_1(state.check, hbuf, 2, 0);
            }
            hold = 0;
            bits = 0;
            state.mode = EXLEN;
          /* falls through */
          case EXLEN:
            if (state.flags & 1024) {
              while (bits < 16) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              state.length = hold;
              if (state.head) {
                state.head.extra_len = hold;
              }
              if (state.flags & 512 && state.wrap & 4) {
                hbuf[0] = hold & 255;
                hbuf[1] = hold >>> 8 & 255;
                state.check = crc32_1(state.check, hbuf, 2, 0);
              }
              hold = 0;
              bits = 0;
            } else if (state.head) {
              state.head.extra = null;
            }
            state.mode = EXTRA;
          /* falls through */
          case EXTRA:
            if (state.flags & 1024) {
              copy = state.length;
              if (copy > have) {
                copy = have;
              }
              if (copy) {
                if (state.head) {
                  len = state.head.extra_len - state.length;
                  if (!state.head.extra) {
                    state.head.extra = new Uint8Array(state.head.extra_len);
                  }
                  state.head.extra.set(
                    input.subarray(
                      next,
                      // extra field is limited to 65536 bytes
                      // - no need for additional size check
                      next + copy
                    ),
                    /*len + copy > state.head.extra_max - len ? state.head.extra_max : copy,*/
                    len
                  );
                }
                if (state.flags & 512 && state.wrap & 4) {
                  state.check = crc32_1(state.check, input, copy, next);
                }
                have -= copy;
                next += copy;
                state.length -= copy;
              }
              if (state.length) {
                break inf_leave;
              }
            }
            state.length = 0;
            state.mode = NAME;
          /* falls through */
          case NAME:
            if (state.flags & 2048) {
              if (have === 0) {
                break inf_leave;
              }
              copy = 0;
              do {
                len = input[next + copy++];
                if (state.head && len && state.length < 65536) {
                  state.head.name += String.fromCharCode(len);
                }
              } while (len && copy < have);
              if (state.flags & 512 && state.wrap & 4) {
                state.check = crc32_1(state.check, input, copy, next);
              }
              have -= copy;
              next += copy;
              if (len) {
                break inf_leave;
              }
            } else if (state.head) {
              state.head.name = null;
            }
            state.length = 0;
            state.mode = COMMENT;
          /* falls through */
          case COMMENT:
            if (state.flags & 4096) {
              if (have === 0) {
                break inf_leave;
              }
              copy = 0;
              do {
                len = input[next + copy++];
                if (state.head && len && state.length < 65536) {
                  state.head.comment += String.fromCharCode(len);
                }
              } while (len && copy < have);
              if (state.flags & 512 && state.wrap & 4) {
                state.check = crc32_1(state.check, input, copy, next);
              }
              have -= copy;
              next += copy;
              if (len) {
                break inf_leave;
              }
            } else if (state.head) {
              state.head.comment = null;
            }
            state.mode = HCRC;
          /* falls through */
          case HCRC:
            if (state.flags & 512) {
              while (bits < 16) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              if (state.wrap & 4 && hold !== (state.check & 65535)) {
                strm.msg = "header crc mismatch";
                state.mode = BAD2;
                break;
              }
              hold = 0;
              bits = 0;
            }
            if (state.head) {
              state.head.hcrc = state.flags >> 9 & 1;
              state.head.done = true;
            }
            strm.adler = state.check = 0;
            state.mode = TYPE2;
            break;
          case DICTID:
            while (bits < 32) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            strm.adler = state.check = zswap32(hold);
            hold = 0;
            bits = 0;
            state.mode = DICT;
          /* falls through */
          case DICT:
            if (state.havedict === 0) {
              strm.next_out = put;
              strm.avail_out = left;
              strm.next_in = next;
              strm.avail_in = have;
              state.hold = hold;
              state.bits = bits;
              return Z_NEED_DICT$1;
            }
            strm.adler = state.check = 1;
            state.mode = TYPE2;
          /* falls through */
          case TYPE2:
            if (flush === Z_BLOCK || flush === Z_TREES) {
              break inf_leave;
            }
          /* falls through */
          case TYPEDO:
            if (state.last) {
              hold >>>= bits & 7;
              bits -= bits & 7;
              state.mode = CHECK;
              break;
            }
            while (bits < 3) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            state.last = hold & 1;
            hold >>>= 1;
            bits -= 1;
            switch (hold & 3) {
              case 0:
                state.mode = STORED3;
                break;
              case 1:
                fixedtables(state);
                state.mode = LEN_;
                if (flush === Z_TREES) {
                  hold >>>= 2;
                  bits -= 2;
                  break inf_leave;
                }
                break;
              case 2:
                state.mode = TABLE2;
                break;
              case 3:
                strm.msg = "invalid block type";
                state.mode = BAD2;
            }
            hold >>>= 2;
            bits -= 2;
            break;
          case STORED3:
            hold >>>= bits & 7;
            bits -= bits & 7;
            while (bits < 32) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if ((hold & 65535) !== (hold >>> 16 ^ 65535)) {
              strm.msg = "invalid stored block lengths";
              state.mode = BAD2;
              break;
            }
            state.length = hold & 65535;
            hold = 0;
            bits = 0;
            state.mode = COPY_;
            if (flush === Z_TREES) {
              break inf_leave;
            }
          /* falls through */
          case COPY_:
            state.mode = COPY2;
          /* falls through */
          case COPY2:
            copy = state.length;
            if (copy) {
              if (copy > have) {
                copy = have;
              }
              if (copy > left) {
                copy = left;
              }
              if (copy === 0) {
                break inf_leave;
              }
              output.set(input.subarray(next, next + copy), put);
              have -= copy;
              next += copy;
              left -= copy;
              put += copy;
              state.length -= copy;
              break;
            }
            state.mode = TYPE2;
            break;
          case TABLE2:
            while (bits < 14) {
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            state.nlen = (hold & 31) + 257;
            hold >>>= 5;
            bits -= 5;
            state.ndist = (hold & 31) + 1;
            hold >>>= 5;
            bits -= 5;
            state.ncode = (hold & 15) + 4;
            hold >>>= 4;
            bits -= 4;
            if (state.nlen > 286 || state.ndist > 30) {
              strm.msg = "too many length or distance symbols";
              state.mode = BAD2;
              break;
            }
            state.have = 0;
            state.mode = LENLENS;
          /* falls through */
          case LENLENS:
            while (state.have < state.ncode) {
              while (bits < 3) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              state.lens[order[state.have++]] = hold & 7;
              hold >>>= 3;
              bits -= 3;
            }
            while (state.have < 19) {
              state.lens[order[state.have++]] = 0;
            }
            state.lencode = state.lendyn;
            state.lenbits = 7;
            opts = { bits: state.lenbits };
            ret = inftrees(CODES2, state.lens, 0, 19, state.lencode, 0, state.work, opts);
            state.lenbits = opts.bits;
            if (ret) {
              strm.msg = "invalid code lengths set";
              state.mode = BAD2;
              break;
            }
            state.have = 0;
            state.mode = CODELENS;
          /* falls through */
          case CODELENS:
            while (state.have < state.nlen + state.ndist) {
              for (; ; ) {
                here = state.lencode[hold & (1 << state.lenbits) - 1];
                here_bits = here >>> 24;
                here_op = here >>> 16 & 255;
                here_val = here & 65535;
                if (here_bits <= bits) {
                  break;
                }
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              if (here_val < 16) {
                hold >>>= here_bits;
                bits -= here_bits;
                state.lens[state.have++] = here_val;
              } else {
                if (here_val === 16) {
                  n = here_bits + 2;
                  while (bits < n) {
                    if (have === 0) {
                      break inf_leave;
                    }
                    have--;
                    hold += input[next++] << bits;
                    bits += 8;
                  }
                  hold >>>= here_bits;
                  bits -= here_bits;
                  if (state.have === 0) {
                    strm.msg = "invalid bit length repeat";
                    state.mode = BAD2;
                    break;
                  }
                  len = state.lens[state.have - 1];
                  copy = 3 + (hold & 3);
                  hold >>>= 2;
                  bits -= 2;
                } else if (here_val === 17) {
                  n = here_bits + 3;
                  while (bits < n) {
                    if (have === 0) {
                      break inf_leave;
                    }
                    have--;
                    hold += input[next++] << bits;
                    bits += 8;
                  }
                  hold >>>= here_bits;
                  bits -= here_bits;
                  len = 0;
                  copy = 3 + (hold & 7);
                  hold >>>= 3;
                  bits -= 3;
                } else {
                  n = here_bits + 7;
                  while (bits < n) {
                    if (have === 0) {
                      break inf_leave;
                    }
                    have--;
                    hold += input[next++] << bits;
                    bits += 8;
                  }
                  hold >>>= here_bits;
                  bits -= here_bits;
                  len = 0;
                  copy = 11 + (hold & 127);
                  hold >>>= 7;
                  bits -= 7;
                }
                if (state.have + copy > state.nlen + state.ndist) {
                  strm.msg = "invalid bit length repeat";
                  state.mode = BAD2;
                  break;
                }
                while (copy--) {
                  state.lens[state.have++] = len;
                }
              }
            }
            if (state.mode === BAD2) {
              break;
            }
            if (state.lens[256] === 0) {
              strm.msg = "invalid code -- missing end-of-block";
              state.mode = BAD2;
              break;
            }
            state.lenbits = 9;
            opts = { bits: state.lenbits };
            ret = inftrees(LENS2, state.lens, 0, state.nlen, state.lencode, 0, state.work, opts);
            state.lenbits = opts.bits;
            if (ret) {
              strm.msg = "invalid literal/lengths set";
              state.mode = BAD2;
              break;
            }
            state.distbits = 6;
            state.distcode = state.distdyn;
            opts = { bits: state.distbits };
            ret = inftrees(DISTS, state.lens, state.nlen, state.ndist, state.distcode, 0, state.work, opts);
            state.distbits = opts.bits;
            if (ret) {
              strm.msg = "invalid distances set";
              state.mode = BAD2;
              break;
            }
            state.mode = LEN_;
            if (flush === Z_TREES) {
              break inf_leave;
            }
          /* falls through */
          case LEN_:
            state.mode = LEN2;
          /* falls through */
          case LEN2:
            if (have >= 6 && left >= 258) {
              strm.next_out = put;
              strm.avail_out = left;
              strm.next_in = next;
              strm.avail_in = have;
              state.hold = hold;
              state.bits = bits;
              inffast(strm, _out);
              put = strm.next_out;
              output = strm.output;
              left = strm.avail_out;
              next = strm.next_in;
              input = strm.input;
              have = strm.avail_in;
              hold = state.hold;
              bits = state.bits;
              if (state.mode === TYPE2) {
                state.back = -1;
              }
              break;
            }
            state.back = 0;
            for (; ; ) {
              here = state.lencode[hold & (1 << state.lenbits) - 1];
              here_bits = here >>> 24;
              here_op = here >>> 16 & 255;
              here_val = here & 65535;
              if (here_bits <= bits) {
                break;
              }
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if (here_op && (here_op & 240) === 0) {
              last_bits = here_bits;
              last_op = here_op;
              last_val = here_val;
              for (; ; ) {
                here = state.lencode[last_val + ((hold & (1 << last_bits + last_op) - 1) >> last_bits)];
                here_bits = here >>> 24;
                here_op = here >>> 16 & 255;
                here_val = here & 65535;
                if (last_bits + here_bits <= bits) {
                  break;
                }
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              hold >>>= last_bits;
              bits -= last_bits;
              state.back += last_bits;
            }
            hold >>>= here_bits;
            bits -= here_bits;
            state.back += here_bits;
            state.length = here_val;
            if (here_op === 0) {
              state.mode = LIT2;
              break;
            }
            if (here_op & 32) {
              state.back = -1;
              state.mode = TYPE2;
              break;
            }
            if (here_op & 64) {
              strm.msg = "invalid literal/length code";
              state.mode = BAD2;
              break;
            }
            state.extra = here_op & 15;
            state.mode = LENEXT2;
          /* falls through */
          case LENEXT2:
            if (state.extra) {
              n = state.extra;
              while (bits < n) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              state.length += hold & (1 << state.extra) - 1;
              hold >>>= state.extra;
              bits -= state.extra;
              state.back += state.extra;
            }
            state.was = state.length;
            state.mode = DIST2;
          /* falls through */
          case DIST2:
            for (; ; ) {
              here = state.distcode[hold & (1 << state.distbits) - 1];
              here_bits = here >>> 24;
              here_op = here >>> 16 & 255;
              here_val = here & 65535;
              if (here_bits <= bits) {
                break;
              }
              if (have === 0) {
                break inf_leave;
              }
              have--;
              hold += input[next++] << bits;
              bits += 8;
            }
            if ((here_op & 240) === 0) {
              last_bits = here_bits;
              last_op = here_op;
              last_val = here_val;
              for (; ; ) {
                here = state.distcode[last_val + ((hold & (1 << last_bits + last_op) - 1) >> last_bits)];
                here_bits = here >>> 24;
                here_op = here >>> 16 & 255;
                here_val = here & 65535;
                if (last_bits + here_bits <= bits) {
                  break;
                }
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              hold >>>= last_bits;
              bits -= last_bits;
              state.back += last_bits;
            }
            hold >>>= here_bits;
            bits -= here_bits;
            state.back += here_bits;
            if (here_op & 64) {
              strm.msg = "invalid distance code";
              state.mode = BAD2;
              break;
            }
            state.offset = here_val;
            state.extra = here_op & 15;
            state.mode = DISTEXT2;
          /* falls through */
          case DISTEXT2:
            if (state.extra) {
              n = state.extra;
              while (bits < n) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              state.offset += hold & (1 << state.extra) - 1;
              hold >>>= state.extra;
              bits -= state.extra;
              state.back += state.extra;
            }
            if (state.offset > state.dmax) {
              strm.msg = "invalid distance too far back";
              state.mode = BAD2;
              break;
            }
            state.mode = MATCH;
          /* falls through */
          case MATCH:
            if (left === 0) {
              break inf_leave;
            }
            copy = _out - left;
            if (state.offset > copy) {
              copy = state.offset - copy;
              if (copy > state.whave) {
                if (state.sane) {
                  strm.msg = "invalid distance too far back";
                  state.mode = BAD2;
                  break;
                }
              }
              if (copy > state.wnext) {
                copy -= state.wnext;
                from = state.wsize - copy;
              } else {
                from = state.wnext - copy;
              }
              if (copy > state.length) {
                copy = state.length;
              }
              from_source = state.window;
            } else {
              from_source = output;
              from = put - state.offset;
              copy = state.length;
            }
            if (copy > left) {
              copy = left;
            }
            left -= copy;
            state.length -= copy;
            do {
              output[put++] = from_source[from++];
            } while (--copy);
            if (state.length === 0) {
              state.mode = LEN2;
            }
            break;
          case LIT2:
            if (left === 0) {
              break inf_leave;
            }
            output[put++] = state.length;
            left--;
            state.mode = LEN2;
            break;
          case CHECK:
            if (state.wrap) {
              while (bits < 32) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold |= input[next++] << bits;
                bits += 8;
              }
              _out -= left;
              strm.total_out += _out;
              state.total += _out;
              if (state.wrap & 4 && _out) {
                strm.adler = state.check = /*UPDATE_CHECK(state.check, put - _out, _out);*/
                state.flags ? crc32_1(state.check, output, _out, put - _out) : adler32_1(state.check, output, _out, put - _out);
              }
              _out = left;
              if (state.wrap & 4 && (state.flags ? hold : zswap32(hold)) !== state.check) {
                strm.msg = "incorrect data check";
                state.mode = BAD2;
                break;
              }
              hold = 0;
              bits = 0;
            }
            state.mode = LENGTH;
          /* falls through */
          case LENGTH:
            if (state.wrap && state.flags) {
              while (bits < 32) {
                if (have === 0) {
                  break inf_leave;
                }
                have--;
                hold += input[next++] << bits;
                bits += 8;
              }
              if (state.wrap & 4 && hold !== (state.total & 4294967295)) {
                strm.msg = "incorrect length check";
                state.mode = BAD2;
                break;
              }
              hold = 0;
              bits = 0;
            }
            state.mode = DONE2;
          /* falls through */
          case DONE2:
            ret = Z_STREAM_END$1;
            break inf_leave;
          case BAD2:
            ret = Z_DATA_ERROR$1;
            break inf_leave;
          case MEM:
            return Z_MEM_ERROR$1;
          case SYNC:
          /* falls through */
          default:
            return Z_STREAM_ERROR$1;
        }
      }
    strm.next_out = put;
    strm.avail_out = left;
    strm.next_in = next;
    strm.avail_in = have;
    state.hold = hold;
    state.bits = bits;
    if (state.wsize || _out !== strm.avail_out && state.mode < BAD2 && (state.mode < CHECK || flush !== Z_FINISH$1)) {
      if (updatewindow(strm, strm.output, strm.next_out, _out - strm.avail_out)) ;
    }
    _in -= strm.avail_in;
    _out -= strm.avail_out;
    strm.total_in += _in;
    strm.total_out += _out;
    state.total += _out;
    if (state.wrap & 4 && _out) {
      strm.adler = state.check = /*UPDATE_CHECK(state.check, strm.next_out - _out, _out);*/
      state.flags ? crc32_1(state.check, output, _out, strm.next_out - _out) : adler32_1(state.check, output, _out, strm.next_out - _out);
    }
    strm.data_type = state.bits + (state.last ? 64 : 0) + (state.mode === TYPE2 ? 128 : 0) + (state.mode === LEN_ || state.mode === COPY_ ? 256 : 0);
    if ((_in === 0 && _out === 0 || flush === Z_FINISH$1) && ret === Z_OK$1) {
      ret = Z_BUF_ERROR3;
    }
    return ret;
  };
  var inflateEnd = (strm) => {
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    let state = strm.state;
    if (state.window) {
      state.window = null;
    }
    strm.state = null;
    return Z_OK$1;
  };
  var inflateGetHeader = (strm, head) => {
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    const state = strm.state;
    if ((state.wrap & 2) === 0) {
      return Z_STREAM_ERROR$1;
    }
    state.head = head;
    head.done = false;
    return Z_OK$1;
  };
  var inflateSetDictionary = (strm, dictionary) => {
    const dictLength = dictionary.length;
    let state;
    let dictid;
    let ret;
    if (inflateStateCheck(strm)) {
      return Z_STREAM_ERROR$1;
    }
    state = strm.state;
    if (state.wrap !== 0 && state.mode !== DICT) {
      return Z_STREAM_ERROR$1;
    }
    if (state.mode === DICT) {
      dictid = 1;
      dictid = adler32_1(dictid, dictionary, dictLength, 0);
      if (dictid !== state.check) {
        return Z_DATA_ERROR$1;
      }
    }
    ret = updatewindow(strm, dictionary, dictLength, dictLength);
    if (ret) {
      state.mode = MEM;
      return Z_MEM_ERROR$1;
    }
    state.havedict = 1;
    return Z_OK$1;
  };
  var inflateReset_1 = inflateReset;
  var inflateReset2_1 = inflateReset2;
  var inflateResetKeep_1 = inflateResetKeep;
  var inflateInit_1 = inflateInit;
  var inflateInit2_1 = inflateInit2;
  var inflate_2$1 = inflate$2;
  var inflateEnd_1 = inflateEnd;
  var inflateGetHeader_1 = inflateGetHeader;
  var inflateSetDictionary_1 = inflateSetDictionary;
  var inflateInfo = "pako inflate (from Nodeca project)";
  var inflate_1$2 = {
    inflateReset: inflateReset_1,
    inflateReset2: inflateReset2_1,
    inflateResetKeep: inflateResetKeep_1,
    inflateInit: inflateInit_1,
    inflateInit2: inflateInit2_1,
    inflate: inflate_2$1,
    inflateEnd: inflateEnd_1,
    inflateGetHeader: inflateGetHeader_1,
    inflateSetDictionary: inflateSetDictionary_1,
    inflateInfo
  };
  function GZheader() {
    this.text = 0;
    this.time = 0;
    this.xflags = 0;
    this.os = 0;
    this.extra = null;
    this.extra_len = 0;
    this.name = "";
    this.comment = "";
    this.hcrc = 0;
    this.done = false;
  }
  var gzheader = GZheader;
  var toString = Object.prototype.toString;
  var {
    Z_NO_FLUSH: Z_NO_FLUSH3,
    Z_FINISH: Z_FINISH3,
    Z_OK: Z_OK3,
    Z_STREAM_END: Z_STREAM_END3,
    Z_NEED_DICT: Z_NEED_DICT3,
    Z_STREAM_ERROR: Z_STREAM_ERROR3,
    Z_DATA_ERROR: Z_DATA_ERROR3,
    Z_MEM_ERROR: Z_MEM_ERROR2
  } = constants$2;
  function Inflate$1(options) {
    this.options = common.assign({
      chunkSize: 1024 * 64,
      windowBits: 15,
      to: ""
    }, options || {});
    const opt = this.options;
    if (opt.raw && opt.windowBits >= 0 && opt.windowBits < 16) {
      opt.windowBits = -opt.windowBits;
      if (opt.windowBits === 0) {
        opt.windowBits = -15;
      }
    }
    if (opt.windowBits >= 0 && opt.windowBits < 16 && !(options && options.windowBits)) {
      opt.windowBits += 32;
    }
    if (opt.windowBits > 15 && opt.windowBits < 48) {
      if ((opt.windowBits & 15) === 0) {
        opt.windowBits |= 15;
      }
    }
    this.err = 0;
    this.msg = "";
    this.ended = false;
    this.chunks = [];
    this.strm = new zstream();
    this.strm.avail_out = 0;
    let status = inflate_1$2.inflateInit2(
      this.strm,
      opt.windowBits
    );
    if (status !== Z_OK3) {
      throw new Error(messages[status]);
    }
    this.header = new gzheader();
    inflate_1$2.inflateGetHeader(this.strm, this.header);
    if (opt.dictionary) {
      if (typeof opt.dictionary === "string") {
        opt.dictionary = strings.string2buf(opt.dictionary);
      } else if (toString.call(opt.dictionary) === "[object ArrayBuffer]") {
        opt.dictionary = new Uint8Array(opt.dictionary);
      }
      if (opt.raw) {
        status = inflate_1$2.inflateSetDictionary(this.strm, opt.dictionary);
        if (status !== Z_OK3) {
          throw new Error(messages[status]);
        }
      }
    }
  }
  Inflate$1.prototype.push = function(data, flush_mode) {
    const strm = this.strm;
    const chunkSize = this.options.chunkSize;
    const dictionary = this.options.dictionary;
    let status, _flush_mode, last_avail_out;
    if (this.ended) return false;
    if (flush_mode === ~~flush_mode) _flush_mode = flush_mode;
    else _flush_mode = flush_mode === true ? Z_FINISH3 : Z_NO_FLUSH3;
    if (toString.call(data) === "[object ArrayBuffer]") {
      strm.input = new Uint8Array(data);
    } else {
      strm.input = data;
    }
    strm.next_in = 0;
    strm.avail_in = strm.input.length;
    for (; ; ) {
      if (strm.avail_out === 0) {
        strm.output = new Uint8Array(chunkSize);
        strm.next_out = 0;
        strm.avail_out = chunkSize;
      }
      status = inflate_1$2.inflate(strm, _flush_mode);
      if (status === Z_NEED_DICT3 && dictionary) {
        status = inflate_1$2.inflateSetDictionary(strm, dictionary);
        if (status === Z_OK3) {
          status = inflate_1$2.inflate(strm, _flush_mode);
        } else if (status === Z_DATA_ERROR3) {
          status = Z_NEED_DICT3;
        }
      }
      while (strm.avail_in > 0 && status === Z_STREAM_END3 && strm.state.wrap > 0 && data[strm.next_in] !== 0) {
        inflate_1$2.inflateReset(strm);
        status = inflate_1$2.inflate(strm, _flush_mode);
      }
      switch (status) {
        case Z_STREAM_ERROR3:
        case Z_DATA_ERROR3:
        case Z_NEED_DICT3:
        case Z_MEM_ERROR2:
          this.onEnd(status);
          this.ended = true;
          return false;
      }
      last_avail_out = strm.avail_out;
      if (strm.next_out) {
        if (strm.avail_out === 0 || status === Z_STREAM_END3) {
          if (this.options.to === "string") {
            let next_out_utf8 = strings.utf8border(strm.output, strm.next_out);
            let tail = strm.next_out - next_out_utf8;
            let utf8str = strings.buf2string(strm.output, next_out_utf8);
            strm.next_out = tail;
            strm.avail_out = chunkSize - tail;
            if (tail) strm.output.set(strm.output.subarray(next_out_utf8, next_out_utf8 + tail), 0);
            this.onData(utf8str);
          } else {
            this.onData(strm.output.length === strm.next_out ? strm.output : strm.output.subarray(0, strm.next_out));
          }
        }
      }
      if (status === Z_OK3 && last_avail_out === 0) continue;
      if (status === Z_STREAM_END3) {
        status = inflate_1$2.inflateEnd(this.strm);
        this.onEnd(status);
        this.ended = true;
        return true;
      }
      if (strm.avail_in === 0) break;
    }
    return true;
  };
  Inflate$1.prototype.onData = function(chunk) {
    this.chunks.push(chunk);
  };
  Inflate$1.prototype.onEnd = function(status) {
    if (status === Z_OK3) {
      if (this.options.to === "string") {
        this.result = this.chunks.join("");
      } else {
        this.result = common.flattenChunks(this.chunks);
      }
    }
    this.chunks = [];
    this.err = status;
    this.msg = this.strm.msg;
  };
  function inflate$1(input, options) {
    const inflator = new Inflate$1(options);
    inflator.push(input);
    if (inflator.err) throw inflator.msg || messages[inflator.err];
    return inflator.result;
  }
  function inflateRaw$1(input, options) {
    options = options || {};
    options.raw = true;
    return inflate$1(input, options);
  }
  var Inflate_1$1 = Inflate$1;
  var inflate_2 = inflate$1;
  var inflateRaw_1$1 = inflateRaw$1;
  var ungzip$1 = inflate$1;
  var constants = constants$2;
  var inflate_1$1 = {
    Inflate: Inflate_1$1,
    inflate: inflate_2,
    inflateRaw: inflateRaw_1$1,
    ungzip: ungzip$1,
    constants
  };
  var { Deflate: Deflate2, deflate, deflateRaw, gzip } = deflate_1$1;
  var { Inflate: Inflate2, inflate, inflateRaw, ungzip } = inflate_1$1;
  var Deflate_1 = Deflate2;
  var deflate_1 = deflate;
  var deflateRaw_1 = deflateRaw;
  var gzip_1 = gzip;
  var Inflate_1 = Inflate2;
  var inflate_1 = inflate;
  var inflateRaw_1 = inflateRaw;
  var ungzip_1 = ungzip;
  var constants_1 = constants$2;
  var pako = {
    Deflate: Deflate_1,
    deflate: deflate_1,
    deflateRaw: deflateRaw_1,
    gzip: gzip_1,
    Inflate: Inflate_1,
    inflate: inflate_1,
    inflateRaw: inflateRaw_1,
    ungzip: ungzip_1,
    constants: constants_1
  };

  // src/Configuration/SampleRankConfiguration.ts
  var SampleRankConfiguration = class {
    includePlay(p) {
      return true;
    }
    getAlbumScore(a) {
      const numDistinctSongsPlayed = a.getNumDistinctSongsPlayed();
      if (numDistinctSongsPlayed < 6) {
        return 0;
      }
      const numPlaysOfNthMostPlayedSong = numDistinctSongsPlayed < 10 ? a.getNumPlaysOfNthMostPlayedSong(numDistinctSongsPlayed) : a.getNumPlaysOfNthMostPlayedSong(10);
      return numPlaysOfNthMostPlayedSong > 1 ? numPlaysOfNthMostPlayedSong : 0;
    }
    includeAlbum(a) {
      return this.getAlbumScore(a) > 0;
    }
  };

  // src/DatabaseHandler.ts
  var DatabaseHandler = class {
    constructor() {
    }
    write(input, onSuccess, onError) {
      const request = indexedDB.open("MyDatabase", 1);
      request.onupgradeneeded = function(event) {
        const db = event.target.result;
        if (!db.objectStoreNames.contains("MyObjectStore")) {
          db.createObjectStore("MyObjectStore", { keyPath: "id" });
        }
      };
      request.onsuccess = (event) => {
        const db = event.target.result;
        const transaction = db.transaction("MyObjectStore", "readwrite");
        const objectStore = transaction.objectStore("MyObjectStore");
        const addRequest = objectStore.put({ id: 1, value: input });
        addRequest.onsuccess = () => {
          onSuccess();
        };
        addRequest.onerror = function() {
          onError(addRequest.error);
        };
      };
      request.onerror = function() {
        alert("Failed to open database: " + request.error);
      };
    }
    async read() {
      return new Promise((resolve, reject) => {
        const request = indexedDB.open("MyDatabase", 1);
        request.onupgradeneeded = function(event) {
          const db = event.target.result;
          if (!db.objectStoreNames.contains("MyObjectStore")) {
            db.createObjectStore("MyObjectStore", { keyPath: "id" });
          }
        };
        request.onsuccess = (event) => {
          const db = event.target.result;
          const transaction = db.transaction("MyObjectStore", "readwrite");
          const objectStore = transaction.objectStore("MyObjectStore");
          const getRequest = objectStore.get(1);
          getRequest.onsuccess = () => {
            resolve(getRequest.result?.value);
          };
          getRequest.onerror = function() {
            reject(getRequest.error);
          };
        };
        request.onerror = function() {
          alert("Failed to open database: " + request.error);
        };
      });
    }
  };

  // src/main.ts
  var fileInput = document.getElementById("file-input");
  var startInput = document.getElementById("startMonthIndex");
  var endInput = document.getElementById("endMonthIndex");
  var startOutput = document.getElementById("startMonthText");
  var endOutput = document.getElementById("endMonthText");
  var postUploadElements = document.getElementsByClassName("post-upload");
  var preUploadElements = document.getElementsByClassName("pre-upload");
  var loadingElements = document.getElementsByClassName("loading");
  var yearSelectorElement = document.getElementById("year-selector");
  var typeSelectorFieldSet = document.getElementById("type-selector");
  var monthSelectorFieldSet = document.getElementById("month-selector");
  var yearSelectorFieldSet = document.getElementById("year-selector");
  var listHeaderQualifierElement = document.getElementById("list-header-qualifier");
  var controlsElement = document.getElementById("controls-container");
  var token = localStorage.getItem("access_token");
  var config2 = new SampleRankConfiguration();
  function decompressPlays(b64encoded) {
    function decodeBase64ToUint8Array(base64String) {
      const binaryString = atob(base64String);
      const uint8Array = new Uint8Array(binaryString.length);
      for (let i = 0; i < binaryString.length; i++) {
        uint8Array[i] = binaryString.charCodeAt(i);
      }
      return uint8Array;
    }
    const data = decodeBase64ToUint8Array(b64encoded);
    const decompressed = pako.inflate(data, { to: "string" });
    return JSON.parse(decompressed, (k, v) => {
      if (k === "ts" && typeof v === "string") {
        return new Date(v);
      }
      return v;
    });
  }
  function compressPlays(plays) {
    function encodeUint8ArrayToBase64(uint8Array) {
      const binaryString = Array.from(uint8Array).map((byte) => String.fromCharCode(byte)).join("");
      return btoa(binaryString);
    }
    const data = JSON.stringify(plays);
    console.log(data.length);
    const compressedStringBuffer = pako.gzip(data);
    return encodeUint8ArrayToBase64(compressedStringBuffer);
  }
  function generateRandomString() {
    const possible = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    const values = crypto.getRandomValues(new Uint8Array(64));
    return values.reduce((acc, x) => acc + possible[x % possible.length], "");
  }
  async function sha256(plain) {
    const encoder = new TextEncoder();
    const data = encoder.encode(plain);
    return window.crypto.subtle.digest("SHA-256", data);
  }
  function base64encode(input) {
    return btoa(String.fromCharCode(...new Uint8Array(input))).replace(/=/g, "").replace(/\+/g, "-").replace(/\//g, "_");
  }
  function createYearRadioButtons(plays) {
    const startDate = plays[0].ts;
    const endDate = plays[plays.length - 1].ts;
    const initialYear = endDate.getFullYear();
    const startYear = startDate.getFullYear();
    const endYear = endDate.getFullYear();
    const fragment = document.createDocumentFragment();
    for (let year = startYear; year <= endYear; year++) {
      const radioButton = createRadioButton(
        year.toString(),
        year.toString(),
        initialYear === year,
        (e2) => {
          setRadioValue("month", "january");
          updateSelectionFromUi(plays);
        }
      );
      fragment.appendChild(radioButton);
    }
    yearSelectorElement.appendChild(fragment);
  }
  function createRadioButton(labelText, value, isChecked, changeHandler) {
    const label = document.createElement("label");
    label.setAttribute("for", "year-" + value);
    const input = document.createElement("input");
    input.type = "radio";
    input.id = "year-" + value;
    input.name = "year";
    input.value = value;
    input.checked = isChecked;
    input.addEventListener("change", changeHandler);
    const fragment = document.createElement("div");
    label.appendChild(document.createTextNode(labelText));
    fragment.appendChild(input);
    fragment.appendChild(label);
    return fragment;
  }
  function getTopNAlbumsForDisplay(filteredPlays, n) {
    const albumCollection = new AlbumCollection();
    filteredPlays.forEach((p) => {
      albumCollection.addPlay(p);
    });
    const promises = albumCollection.getAlbums().filter((a) => config2.includeAlbum(a)).sort((a, b) => config2.getAlbumScore(b) - config2.getAlbumScore(a)).slice(0, n).map(async (a) => {
      const arbitraryTrackId = a.getArbitraryTrackId();
      let imageUrl;
      if (arbitraryTrackId) {
        imageUrl = await getImageUrlForTrack(arbitraryTrackId, token);
      } else {
        imageUrl = null;
      }
      return new AlbumForDisplay(
        a.albumName,
        a.artistName,
        imageUrl
      );
    });
    return Promise.all(promises);
  }
  function drawAlbumsToUi(albums) {
    const listElement = document.getElementById("album-list");
    listElement.innerHTML = "";
    if (albums.length < 1) {
      const message = document.createElement("p");
      message.className = "no-albums-found-message";
      message.textContent = "No albums found for selected period.";
      listElement.appendChild(message);
      return;
    }
    let i = 1;
    albums.forEach((album) => {
      const albumElement = document.createElement("div");
      albumElement.className = "album";
      const numberElement = document.createElement("span");
      numberElement.className = "album-number";
      numberElement.textContent = (i++).toString();
      albumElement.appendChild(numberElement);
      if (album.imageUrl) {
        const artElement = document.createElement("img");
        artElement.src = album.imageUrl;
        artElement.alt = `Album art for ${album.albumTitle} by ${album.artistName}`;
        artElement.className = "album-art";
        albumElement.appendChild(artElement);
      }
      const albumLabelElement = document.createElement("div");
      albumLabelElement.className = "album-label";
      albumElement.appendChild(albumLabelElement);
      const albumNameElement = document.createElement("span");
      albumNameElement.textContent = album.albumTitle;
      albumNameElement.className = "album-title";
      albumLabelElement.appendChild(albumNameElement);
      const artistNameElement = document.createElement("span");
      artistNameElement.textContent = album.artistName;
      artistNameElement.className = "artist-name";
      albumLabelElement.appendChild(artistNameElement);
      listElement.appendChild(albumElement);
    });
  }
  function getPlaysBetween(plays, startTimeInclusive, endTimeExclusive) {
    return plays.filter(
      (p) => p.ts >= startTimeInclusive && p.ts < endTimeExclusive
    );
  }
  function drawTopAlbumsBetween(plays, startTimeInclusive, endTimeExclusive) {
    const filteredPlays = getPlaysBetween(
      plays.filter(
        (p) => config2.includePlay(p)
      ),
      startTimeInclusive,
      endTimeExclusive
    );
    getTopNAlbumsForDisplay(filteredPlays, 5).then(
      (topNAlbums) => drawAlbumsToUi(topNAlbums)
    );
  }
  function selectAllYears(plays) {
    const firstYearInclusive = plays[0].ts.getFullYear();
    const lastYearInclusive = plays[plays.length - 1].ts.getFullYear();
    const startTimeInclusive = new Date(firstYearInclusive, 0, 1);
    const endTimeExclusive = new Date(lastYearInclusive + 1, 0, 1);
    drawTopAlbumsBetween(plays, startTimeInclusive, endTimeExclusive);
    listHeaderQualifierElement.textContent = "";
  }
  function selectMonth(plays, monthName, year) {
    const monthIndex = [
      "january",
      "february",
      "march",
      "april",
      "may",
      "june",
      "july",
      "august",
      "september",
      "october",
      "november",
      "december"
    ].indexOf(monthName);
    const startTimeInclusive = new Date(year, monthIndex, 1);
    const endTimeExclusive = new Date(year, monthIndex + 1, 1);
    drawTopAlbumsBetween(plays, startTimeInclusive, endTimeExclusive);
    listHeaderQualifierElement.textContent = " of " + monthName.charAt(0).toUpperCase() + monthName.slice(1) + " " + year;
  }
  function selectYear(plays, year) {
    const startTimeInclusive = new Date(year, 0, 1);
    const endTimeExclusive = new Date(year + 1, 0, 1);
    drawTopAlbumsBetween(plays, startTimeInclusive, endTimeExclusive);
    listHeaderQualifierElement.textContent = " of " + year;
  }
  var databaseHandler = new DatabaseHandler();
  function hideLoadingElements() {
    for (let i = 0; i < preUploadElements.length; i++) {
      loadingElements[i].style.display = "none";
    }
  }
  function showPreUploadElements() {
    for (let i = 0; i < preUploadElements.length; i++) {
      preUploadElements[i].style.display = "block";
    }
  }
  alert("page loaded");
  databaseHandler.read().then((compressedPlays) => {
    alert("completed read from indexeddb");
    hideLoadingElements();
    alert("hid loading dialog");
    if (compressedPlays && !reupload) {
      alert("compressedPlays && !reupload");
      const decompressedPlays = decompressPlays(compressedPlays);
      alert("decompressed");
      setUpPostUploadUi(decompressedPlays);
      alert("ui configured");
    } else {
      alert("previously uploaded file not found");
      showPreUploadElements();
      fileInput.addEventListener("change", async () => {
        const file = fileInput.files?.[0];
        if (file) {
          const zipReader = new ZipReader(new BlobReader(file));
          try {
            const plays = [];
            const entries = await zipReader.getEntries();
            for (const entry of entries) {
              if (entry.getData) {
                const filename = entry.filename;
                if (filename.startsWith("Spotify Extended Streaming History/Streaming_History_Audio_")) {
                  const jsonFileContent = await entry.getData(new TextWriter());
                  const playsData = JSON.parse(jsonFileContent);
                  plays.push(...playsData.map((item) => Play.fromJsonObject(item)));
                }
              }
            }
            alert("writing to db");
            databaseHandler.write(
              compressPlays(plays),
              () => {
                alert("wrote to db");
              },
              () => {
                alert("Failed to save file.");
              }
            );
            alert("setting up ui now");
            setUpPostUploadUi(plays);
            alert("ui is ready");
          } catch (e2) {
            console.error(e2);
            alert("Invalid file format.");
          }
          await zipReader.close();
        }
      });
    }
  }).catch((reason) => {
    hideLoadingElements();
    alert(reason);
    showPreUploadElements();
  });
  function updateSelectionFromUi(plays) {
    const selectedYear = parseInt(document.querySelector('input[name="year"]:checked').value);
    const selectedType = document.querySelector('input[name="type"]:checked').value;
    if (selectedType === "month") {
      const selectedMonthName = document.querySelector('input[name="month"]:checked').value;
      selectMonth(plays, selectedMonthName, selectedYear);
    } else if (selectedType === "year") {
      selectYear(plays, selectedYear);
    } else {
      selectAllYears(plays);
    }
  }
  function setRadioValue(name, value) {
    const radios = document.querySelectorAll(`input[name="${name}"]`);
    radios.forEach((radio) => {
      if (radio.value === value) {
        radio.checked = true;
      }
    });
  }
  function setUpPostUploadUi(plays) {
    createYearRadioButtons(plays);
    typeSelectorFieldSet.addEventListener("change", (e2) => {
      controlsElement.classList.remove("selected-type-year");
      controlsElement.classList.remove("selected-type-all-time");
      controlsElement.classList.remove("selected-type-month");
      const selectedType = e2.target.value;
      if (selectedType === "month") {
        controlsElement.classList.add("selected-type-month");
      } else if (selectedType === "year") {
        controlsElement.classList.add("selected-type-year");
      } else {
        controlsElement.classList.add("selected-type-all-time");
      }
      updateSelectionFromUi(plays);
    });
    monthSelectorFieldSet.addEventListener("change", (e2) => {
      updateSelectionFromUi(plays);
    });
    const lastYearInData = plays[plays.length - 1].ts.getFullYear();
    selectYear(plays, lastYearInData);
    for (let i = 0; i < preUploadElements.length; i++) {
      preUploadElements[i].style.display = "none";
    }
    for (let i = 0; i < postUploadElements.length; i++) {
      postUploadElements[i].style.display = "block";
    }
  }
  var { hostname, protocol } = window.location;
  var clientId = "30b34f37fc0d401dbd999d6525a9fff4";
  var isLive = hostname === "tsegarra.github.io";
  var redirectUri = isLive ? "https://tsegarra.github.io/spotify-top-albums" : "http://localhost:8081";
  var rootUri = isLive ? "/spotify-top-albums" : "/";
  var urlParams = new URLSearchParams(window.location.search);
  var code = urlParams.get("code");
  var reupload = urlParams.get("reupload");
  async function getToken(code1, codeVerifier) {
    const payload = {
      method: "POST",
      headers: {
        "Content-Type": "application/x-www-form-urlencoded"
      },
      body: new URLSearchParams({
        client_id: clientId,
        grant_type: "authorization_code",
        code: code1,
        redirect_uri: redirectUri,
        code_verifier: codeVerifier
      })
    };
    const body = await fetch("https://accounts.spotify.com/api/token", payload);
    const response = await body.json();
    setTokenFromResponse(response);
  }
  function setTokenFromResponse(response) {
    localStorage.setItem("access_token", response.access_token);
    localStorage.setItem("refresh_token", response.refresh_token);
    localStorage.setItem("token_expiration", (Date.now() + response.expires_in * 1e3).toString());
  }
  async function refreshUsingRefreshToken(refreshToken2) {
    const payload = {
      method: "POST",
      headers: {
        "Content-Type": "application/x-www-form-urlencoded"
      },
      body: new URLSearchParams({
        client_id: clientId,
        grant_type: "refresh_token",
        refresh_token: refreshToken2
      })
    };
    const response = await fetch("https://accounts.spotify.com/api/token", payload);
    const data = await response.json();
    if (data.access_token) {
      setTokenFromResponse(data);
    } else {
      throw new Error("Failed to refresh token");
    }
  }
  function isTokenExpired() {
    const expirationTime = parseInt(localStorage.getItem("token_expiration") || "0", 10);
    return Date.now() >= expirationTime;
  }
  function cacheImageUrlForTrack(trackId, imageUrl) {
    const storedData = localStorage.getItem("trackImageUrls");
    const trackImageUrls = storedData ? JSON.parse(storedData) : {};
    trackImageUrls[trackId] = imageUrl;
    localStorage.setItem("trackImageUrls", JSON.stringify(trackImageUrls));
  }
  function getImageUrlForTrackFromCache(trackId) {
    const storedData = localStorage.getItem("trackImageUrls");
    if (!storedData) {
      return null;
    }
    const trackImageUrls = JSON.parse(storedData);
    return trackImageUrls[trackId] || null;
  }
  async function getImageUrlForTrack(trackId, token2) {
    const cachedImageUrl = getImageUrlForTrackFromCache(trackId);
    if (cachedImageUrl) {
      return cachedImageUrl;
    }
    const payload = {
      method: "GET",
      headers: {
        "Content-Type": "application/x-www-form-urlencoded",
        "Authorization": `Bearer ${token2}`
      }
    };
    const body = await fetch("https://api.spotify.com/v1/tracks/" + trackId, payload);
    const response = await body.json();
    const imageUrl = response.album.images[0].url;
    cacheImageUrlForTrack(trackId, imageUrl);
    return imageUrl;
  }
  var codeVerifierFromLocalStorage = localStorage.getItem("code_verifier");
  var refreshToken = localStorage.getItem("refresh_token");
  var newTokenIsRequired = isTokenExpired() || !token;
  if (newTokenIsRequired) {
    if (refreshToken) {
      refreshUsingRefreshToken(refreshToken).then(() => {
        window.location.href = rootUri;
      });
    } else if (code && codeVerifierFromLocalStorage) {
      getToken(code, codeVerifierFromLocalStorage).then(() => {
        window.location.href = rootUri;
      });
    } else {
      const codeVerifier = generateRandomString();
      sha256(codeVerifier).then((d) => {
        const codeChallenge = base64encode(d);
        const scope = "user-read-private user-read-email";
        const authUrl = new URL("https://accounts.spotify.com/authorize");
        window.localStorage.setItem("code_verifier", codeVerifier);
        const params = {
          response_type: "code",
          client_id: clientId,
          scope,
          code_challenge_method: "S256",
          code_challenge: codeChallenge,
          redirect_uri: redirectUri
        };
        authUrl.search = new URLSearchParams(params).toString();
        window.location.href = authUrl.toString();
      });
    }
  }
})();
/*! Bundled license information:

pako/dist/pako.esm.mjs:
  (*! pako 2.1.0 https://github.com/nodeca/pako @license (MIT AND Zlib) *)
*/
