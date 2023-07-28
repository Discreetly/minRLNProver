/**
 * @module minrlnprover
 * @version 1.0.0
 * @file 
 * @copyright Privacy and Scaling Explorations 2023
 * @license MIT
 * @see [Github]{@link undefined}
*/
'use strict';

var rlnjs = require('rlnjs');
var discreetlyInterfaces = require('discreetly-interfaces');

/**
 * @module @zk-kit/incremental-merkle-tree
 * @version 1.1.0
 * @file Incremental Merkle tree implementation in TypeScript.
 * @copyright Cedoor 2023
 * @license MIT
 * @see [Github]{@link https://github.com/privacy-scaling-explorations/zk-kit/tree/main/packages/incremental-merkle-tree}
*/
function checkParameter$1(value, name) {
    var types = [];
    for (var _i = 2; _i < arguments.length; _i++) {
        types[_i - 2] = arguments[_i];
    }
    if (value === undefined) {
        throw new TypeError("Parameter '".concat(name, "' is not defined"));
    }
    if (!types.includes(typeof value)) {
        throw new TypeError("Parameter '".concat(name, "' is none of these types: ").concat(types.join(", ")));
    }
}

function createProof(index, depth, arity, nodes, zeroes, root) {
    checkParameter$1(index, "index", "number");
    if (index < 0 || index >= nodes[0].length) {
        throw new Error("The leaf does not exist in this tree");
    }
    var siblings = [];
    var pathIndices = [];
    var leafIndex = index;
    for (var level = 0; level < depth; level += 1) {
        var position = index % arity;
        var levelStartIndex = index - position;
        var levelEndIndex = levelStartIndex + arity;
        pathIndices[level] = position;
        siblings[level] = [];
        for (var i = levelStartIndex; i < levelEndIndex; i += 1) {
            if (i !== index) {
                if (i < nodes[level].length) {
                    siblings[level].push(nodes[level][i]);
                }
                else {
                    siblings[level].push(zeroes[level]);
                }
            }
        }
        index = Math.floor(index / arity);
    }
    return { root: root, leaf: nodes[0][leafIndex], pathIndices: pathIndices, siblings: siblings };
}

function indexOf(leaf, nodes) {
    checkParameter$1(leaf, "leaf", "number", "string", "bigint");
    return nodes[0].indexOf(leaf);
}

function insert(leaf, depth, arity, nodes, zeroes, hash) {
    checkParameter$1(leaf, "leaf", "number", "string", "bigint");
    if (nodes[0].length >= Math.pow(arity, depth)) {
        throw new Error("The tree is full");
    }
    var node = leaf;
    var index = nodes[0].length;
    for (var level = 0; level < depth; level += 1) {
        var position = index % arity;
        var levelStartIndex = index - position;
        var levelEndIndex = levelStartIndex + arity;
        var children = [];
        nodes[level][index] = node;
        for (var i = levelStartIndex; i < levelEndIndex; i += 1) {
            if (i < nodes[level].length) {
                children.push(nodes[level][i]);
            }
            else {
                children.push(zeroes[level]);
            }
        }
        node = hash(children);
        index = Math.floor(index / arity);
    }
    return node;
}

function update(index, value, depth, arity, nodes, zeroes, hash) {
    checkParameter$1(index, "index", "number");
    if (index < 0 || index >= nodes[0].length) {
        throw new Error("The leaf does not exist in this tree");
    }
    var node = value;
    for (var level = 0; level < depth; level += 1) {
        var position = index % arity;
        var levelStartIndex = index - position;
        var levelEndIndex = levelStartIndex + arity;
        var children = [];
        nodes[level][index] = node;
        for (var i = levelStartIndex; i < levelEndIndex; i += 1) {
            if (i < nodes[level].length) {
                children.push(nodes[level][i]);
            }
            else {
                children.push(zeroes[level]);
            }
        }
        node = hash(children);
        index = Math.floor(index / arity);
    }
    return node;
}

function verifyProof(proof, hash) {
    checkParameter$1(proof, "proof", "object");
    checkParameter$1(proof.root, "proof.root", "number", "string", "bigint");
    checkParameter$1(proof.leaf, "proof.leaf", "number", "string", "bigint");
    checkParameter$1(proof.siblings, "proof.siblings", "object");
    checkParameter$1(proof.pathIndices, "proof.pathElements", "object");
    var node = proof.leaf;
    for (var i = 0; i < proof.siblings.length; i += 1) {
        var children = proof.siblings[i].slice();
        children.splice(proof.pathIndices[i], 0, node);
        node = hash(children);
    }
    return proof.root === node;
}

/**
 * A Merkle tree is a tree in which every leaf node is labelled with the cryptographic hash of a
 * data block, and every non-leaf node is labelled with the cryptographic hash of the labels of its child nodes.
 * It allows efficient and secure verification of the contents of large data structures.
 * The IncrementalMerkleTree class is a TypeScript implementation of Incremental Merkle tree and it
 * provides all the functions to create efficient trees and to generate and verify proofs of membership.
 */
var IncrementalMerkleTree = /** @class */ (function () {
    /**
     * Initializes the tree with the hash function, the depth, the zero value to use for zeroes
     * and the arity (i.e. the number of children for each node).
     * @param hash Hash function.
     * @param depth Tree depth.
     * @param zeroValue Zero values for zeroes.
     * @param arity The number of children for each node.
     * @param leaves The list of initial leaves.
     */
    function IncrementalMerkleTree(hash, depth, zeroValue, arity, leaves) {
        if (arity === void 0) { arity = 2; }
        if (leaves === void 0) { leaves = []; }
        var _a;
        checkParameter$1(hash, "hash", "function");
        checkParameter$1(depth, "depth", "number");
        checkParameter$1(zeroValue, "zeroValue", "number", "string", "bigint");
        checkParameter$1(arity, "arity", "number");
        checkParameter$1(leaves, "leaves", "object");
        if (depth < 1 || depth > IncrementalMerkleTree.maxDepth) {
            throw new Error("The tree depth must be between 1 and 32");
        }
        if (leaves.length > Math.pow(arity, depth)) {
            throw new Error("The tree cannot contain more than ".concat(Math.pow(arity, depth), " leaves"));
        }
        // Initialize the attributes.
        this._hash = hash;
        this._depth = depth;
        this._zeroes = [];
        this._nodes = [];
        this._arity = arity;
        for (var level = 0; level < depth; level += 1) {
            this._zeroes.push(zeroValue);
            this._nodes[level] = [];
            // There must be a zero value for each tree level (except the root).
            zeroValue = hash(Array(this._arity).fill(zeroValue));
        }
        this._nodes[depth] = [];
        // It initializes the tree with a list of leaves if there are any.
        if (leaves.length > 0) {
            this._nodes[0] = leaves;
            for (var level = 0; level < depth; level += 1) {
                for (var index = 0; index < Math.ceil(this._nodes[level].length / arity); index += 1) {
                    var position = index * arity;
                    var children = [];
                    for (var i = 0; i < arity; i += 1) {
                        children.push((_a = this._nodes[level][position + i]) !== null && _a !== void 0 ? _a : this.zeroes[level]);
                    }
                    this._nodes[level + 1][index] = hash(children);
                }
            }
        }
        else {
            // If there are no leaves, the default root is the last zero value.
            this._nodes[depth][0] = zeroValue;
        }
        // Freeze the array objects. It prevents unintentional changes.
        Object.freeze(this._zeroes);
        Object.freeze(this._nodes);
    }
    Object.defineProperty(IncrementalMerkleTree.prototype, "root", {
        /**
         * Returns the root hash of the tree.
         * @returns Root hash.
         */
        get: function () {
            return this._nodes[this.depth][0];
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(IncrementalMerkleTree.prototype, "depth", {
        /**
         * Returns the depth of the tree.
         * @returns Tree depth.
         */
        get: function () {
            return this._depth;
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(IncrementalMerkleTree.prototype, "leaves", {
        /**
         * Returns the leaves of the tree.
         * @returns List of leaves.
         */
        get: function () {
            return this._nodes[0].slice();
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(IncrementalMerkleTree.prototype, "zeroes", {
        /**
         * Returns the zeroes nodes of the tree.
         * @returns List of zeroes.
         */
        get: function () {
            return this._zeroes;
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(IncrementalMerkleTree.prototype, "arity", {
        /**
         * Returns the number of children for each node.
         * @returns Number of children per node.
         */
        get: function () {
            return this._arity;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the index of a leaf. If the leaf does not exist it returns -1.
     * @param leaf Tree leaf.
     * @returns Index of the leaf.
     */
    IncrementalMerkleTree.prototype.indexOf = function (leaf) {
        return indexOf(leaf, this._nodes);
    };
    /**
     * Inserts a new leaf in the tree.
     * @param leaf New leaf.
     */
    IncrementalMerkleTree.prototype.insert = function (leaf) {
        this._nodes[this.depth][0] = insert(leaf, this.depth, this.arity, this._nodes, this.zeroes, this._hash);
    };
    /**
     * Deletes a leaf from the tree. It does not remove the leaf from
     * the data structure. It set the leaf to be deleted to a zero value.
     * @param index Index of the leaf to be deleted.
     */
    IncrementalMerkleTree.prototype.delete = function (index) {
        this._nodes[this.depth][0] = update(index, this.zeroes[0], this.depth, this.arity, this._nodes, this.zeroes, this._hash);
    };
    /**
     * Updates a leaf in the tree.
     * @param index Index of the leaf to be updated.
     * @param newLeaf New leaf value.
     */
    IncrementalMerkleTree.prototype.update = function (index, newLeaf) {
        this._nodes[this.depth][0] = update(index, newLeaf, this.depth, this.arity, this._nodes, this.zeroes, this._hash);
    };
    /**
     * Creates a proof of membership.
     * @param index Index of the proof's leaf.
     * @returns Proof object.
     */
    IncrementalMerkleTree.prototype.createProof = function (index) {
        return createProof(index, this.depth, this.arity, this._nodes, this.zeroes, this.root);
    };
    /**
     * Verifies a proof and return true or false.
     * @param proof Proof to be verified.
     * @returns True or false.
     */
    IncrementalMerkleTree.prototype.verifyProof = function (proof) {
        return verifyProof(proof, this._hash);
    };
    IncrementalMerkleTree.maxDepth = 32;
    return IncrementalMerkleTree;
}());

var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function getDefaultExportFromCjs (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

var bn = {exports: {}};

bn.exports;

(function (module) {
	(function (module, exports) {

	  // Utils
	  function assert (val, msg) {
	    if (!val) throw new Error(msg || 'Assertion failed');
	  }

	  // Could use `inherits` module, but don't want to move from single file
	  // architecture yet.
	  function inherits (ctor, superCtor) {
	    ctor.super_ = superCtor;
	    var TempCtor = function () {};
	    TempCtor.prototype = superCtor.prototype;
	    ctor.prototype = new TempCtor();
	    ctor.prototype.constructor = ctor;
	  }

	  // BN

	  function BN (number, base, endian) {
	    if (BN.isBN(number)) {
	      return number;
	    }

	    this.negative = 0;
	    this.words = null;
	    this.length = 0;

	    // Reduction context
	    this.red = null;

	    if (number !== null) {
	      if (base === 'le' || base === 'be') {
	        endian = base;
	        base = 10;
	      }

	      this._init(number || 0, base || 10, endian || 'be');
	    }
	  }
	  if (typeof module === 'object') {
	    module.exports = BN;
	  } else {
	    exports.BN = BN;
	  }

	  BN.BN = BN;
	  BN.wordSize = 26;

	  var Buffer;
	  try {
	    if (typeof window !== 'undefined' && typeof window.Buffer !== 'undefined') {
	      Buffer = window.Buffer;
	    } else {
	      Buffer = require('buffer').Buffer;
	    }
	  } catch (e) {
	  }

	  BN.isBN = function isBN (num) {
	    if (num instanceof BN) {
	      return true;
	    }

	    return num !== null && typeof num === 'object' &&
	      num.constructor.wordSize === BN.wordSize && Array.isArray(num.words);
	  };

	  BN.max = function max (left, right) {
	    if (left.cmp(right) > 0) return left;
	    return right;
	  };

	  BN.min = function min (left, right) {
	    if (left.cmp(right) < 0) return left;
	    return right;
	  };

	  BN.prototype._init = function init (number, base, endian) {
	    if (typeof number === 'number') {
	      return this._initNumber(number, base, endian);
	    }

	    if (typeof number === 'object') {
	      return this._initArray(number, base, endian);
	    }

	    if (base === 'hex') {
	      base = 16;
	    }
	    assert(base === (base | 0) && base >= 2 && base <= 36);

	    number = number.toString().replace(/\s+/g, '');
	    var start = 0;
	    if (number[0] === '-') {
	      start++;
	      this.negative = 1;
	    }

	    if (start < number.length) {
	      if (base === 16) {
	        this._parseHex(number, start, endian);
	      } else {
	        this._parseBase(number, base, start);
	        if (endian === 'le') {
	          this._initArray(this.toArray(), base, endian);
	        }
	      }
	    }
	  };

	  BN.prototype._initNumber = function _initNumber (number, base, endian) {
	    if (number < 0) {
	      this.negative = 1;
	      number = -number;
	    }
	    if (number < 0x4000000) {
	      this.words = [number & 0x3ffffff];
	      this.length = 1;
	    } else if (number < 0x10000000000000) {
	      this.words = [
	        number & 0x3ffffff,
	        (number / 0x4000000) & 0x3ffffff
	      ];
	      this.length = 2;
	    } else {
	      assert(number < 0x20000000000000); // 2 ^ 53 (unsafe)
	      this.words = [
	        number & 0x3ffffff,
	        (number / 0x4000000) & 0x3ffffff,
	        1
	      ];
	      this.length = 3;
	    }

	    if (endian !== 'le') return;

	    // Reverse the bytes
	    this._initArray(this.toArray(), base, endian);
	  };

	  BN.prototype._initArray = function _initArray (number, base, endian) {
	    // Perhaps a Uint8Array
	    assert(typeof number.length === 'number');
	    if (number.length <= 0) {
	      this.words = [0];
	      this.length = 1;
	      return this;
	    }

	    this.length = Math.ceil(number.length / 3);
	    this.words = new Array(this.length);
	    for (var i = 0; i < this.length; i++) {
	      this.words[i] = 0;
	    }

	    var j, w;
	    var off = 0;
	    if (endian === 'be') {
	      for (i = number.length - 1, j = 0; i >= 0; i -= 3) {
	        w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
	        this.words[j] |= (w << off) & 0x3ffffff;
	        this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
	        off += 24;
	        if (off >= 26) {
	          off -= 26;
	          j++;
	        }
	      }
	    } else if (endian === 'le') {
	      for (i = 0, j = 0; i < number.length; i += 3) {
	        w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
	        this.words[j] |= (w << off) & 0x3ffffff;
	        this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
	        off += 24;
	        if (off >= 26) {
	          off -= 26;
	          j++;
	        }
	      }
	    }
	    return this._strip();
	  };

	  function parseHex4Bits (string, index) {
	    var c = string.charCodeAt(index);
	    // '0' - '9'
	    if (c >= 48 && c <= 57) {
	      return c - 48;
	    // 'A' - 'F'
	    } else if (c >= 65 && c <= 70) {
	      return c - 55;
	    // 'a' - 'f'
	    } else if (c >= 97 && c <= 102) {
	      return c - 87;
	    } else {
	      assert(false, 'Invalid character in ' + string);
	    }
	  }

	  function parseHexByte (string, lowerBound, index) {
	    var r = parseHex4Bits(string, index);
	    if (index - 1 >= lowerBound) {
	      r |= parseHex4Bits(string, index - 1) << 4;
	    }
	    return r;
	  }

	  BN.prototype._parseHex = function _parseHex (number, start, endian) {
	    // Create possibly bigger array to ensure that it fits the number
	    this.length = Math.ceil((number.length - start) / 6);
	    this.words = new Array(this.length);
	    for (var i = 0; i < this.length; i++) {
	      this.words[i] = 0;
	    }

	    // 24-bits chunks
	    var off = 0;
	    var j = 0;

	    var w;
	    if (endian === 'be') {
	      for (i = number.length - 1; i >= start; i -= 2) {
	        w = parseHexByte(number, start, i) << off;
	        this.words[j] |= w & 0x3ffffff;
	        if (off >= 18) {
	          off -= 18;
	          j += 1;
	          this.words[j] |= w >>> 26;
	        } else {
	          off += 8;
	        }
	      }
	    } else {
	      var parseLength = number.length - start;
	      for (i = parseLength % 2 === 0 ? start + 1 : start; i < number.length; i += 2) {
	        w = parseHexByte(number, start, i) << off;
	        this.words[j] |= w & 0x3ffffff;
	        if (off >= 18) {
	          off -= 18;
	          j += 1;
	          this.words[j] |= w >>> 26;
	        } else {
	          off += 8;
	        }
	      }
	    }

	    this._strip();
	  };

	  function parseBase (str, start, end, mul) {
	    var r = 0;
	    var b = 0;
	    var len = Math.min(str.length, end);
	    for (var i = start; i < len; i++) {
	      var c = str.charCodeAt(i) - 48;

	      r *= mul;

	      // 'a'
	      if (c >= 49) {
	        b = c - 49 + 0xa;

	      // 'A'
	      } else if (c >= 17) {
	        b = c - 17 + 0xa;

	      // '0' - '9'
	      } else {
	        b = c;
	      }
	      assert(c >= 0 && b < mul, 'Invalid character');
	      r += b;
	    }
	    return r;
	  }

	  BN.prototype._parseBase = function _parseBase (number, base, start) {
	    // Initialize as zero
	    this.words = [0];
	    this.length = 1;

	    // Find length of limb in base
	    for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base) {
	      limbLen++;
	    }
	    limbLen--;
	    limbPow = (limbPow / base) | 0;

	    var total = number.length - start;
	    var mod = total % limbLen;
	    var end = Math.min(total, total - mod) + start;

	    var word = 0;
	    for (var i = start; i < end; i += limbLen) {
	      word = parseBase(number, i, i + limbLen, base);

	      this.imuln(limbPow);
	      if (this.words[0] + word < 0x4000000) {
	        this.words[0] += word;
	      } else {
	        this._iaddn(word);
	      }
	    }

	    if (mod !== 0) {
	      var pow = 1;
	      word = parseBase(number, i, number.length, base);

	      for (i = 0; i < mod; i++) {
	        pow *= base;
	      }

	      this.imuln(pow);
	      if (this.words[0] + word < 0x4000000) {
	        this.words[0] += word;
	      } else {
	        this._iaddn(word);
	      }
	    }

	    this._strip();
	  };

	  BN.prototype.copy = function copy (dest) {
	    dest.words = new Array(this.length);
	    for (var i = 0; i < this.length; i++) {
	      dest.words[i] = this.words[i];
	    }
	    dest.length = this.length;
	    dest.negative = this.negative;
	    dest.red = this.red;
	  };

	  function move (dest, src) {
	    dest.words = src.words;
	    dest.length = src.length;
	    dest.negative = src.negative;
	    dest.red = src.red;
	  }

	  BN.prototype._move = function _move (dest) {
	    move(dest, this);
	  };

	  BN.prototype.clone = function clone () {
	    var r = new BN(null);
	    this.copy(r);
	    return r;
	  };

	  BN.prototype._expand = function _expand (size) {
	    while (this.length < size) {
	      this.words[this.length++] = 0;
	    }
	    return this;
	  };

	  // Remove leading `0` from `this`
	  BN.prototype._strip = function strip () {
	    while (this.length > 1 && this.words[this.length - 1] === 0) {
	      this.length--;
	    }
	    return this._normSign();
	  };

	  BN.prototype._normSign = function _normSign () {
	    // -0 = 0
	    if (this.length === 1 && this.words[0] === 0) {
	      this.negative = 0;
	    }
	    return this;
	  };

	  // Check Symbol.for because not everywhere where Symbol defined
	  // See https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol#Browser_compatibility
	  if (typeof Symbol !== 'undefined' && typeof Symbol.for === 'function') {
	    try {
	      BN.prototype[Symbol.for('nodejs.util.inspect.custom')] = inspect;
	    } catch (e) {
	      BN.prototype.inspect = inspect;
	    }
	  } else {
	    BN.prototype.inspect = inspect;
	  }

	  function inspect () {
	    return (this.red ? '<BN-R: ' : '<BN: ') + this.toString(16) + '>';
	  }

	  /*

	  var zeros = [];
	  var groupSizes = [];
	  var groupBases = [];

	  var s = '';
	  var i = -1;
	  while (++i < BN.wordSize) {
	    zeros[i] = s;
	    s += '0';
	  }
	  groupSizes[0] = 0;
	  groupSizes[1] = 0;
	  groupBases[0] = 0;
	  groupBases[1] = 0;
	  var base = 2 - 1;
	  while (++base < 36 + 1) {
	    var groupSize = 0;
	    var groupBase = 1;
	    while (groupBase < (1 << BN.wordSize) / base) {
	      groupBase *= base;
	      groupSize += 1;
	    }
	    groupSizes[base] = groupSize;
	    groupBases[base] = groupBase;
	  }

	  */

	  var zeros = [
	    '',
	    '0',
	    '00',
	    '000',
	    '0000',
	    '00000',
	    '000000',
	    '0000000',
	    '00000000',
	    '000000000',
	    '0000000000',
	    '00000000000',
	    '000000000000',
	    '0000000000000',
	    '00000000000000',
	    '000000000000000',
	    '0000000000000000',
	    '00000000000000000',
	    '000000000000000000',
	    '0000000000000000000',
	    '00000000000000000000',
	    '000000000000000000000',
	    '0000000000000000000000',
	    '00000000000000000000000',
	    '000000000000000000000000',
	    '0000000000000000000000000'
	  ];

	  var groupSizes = [
	    0, 0,
	    25, 16, 12, 11, 10, 9, 8,
	    8, 7, 7, 7, 7, 6, 6,
	    6, 6, 6, 6, 6, 5, 5,
	    5, 5, 5, 5, 5, 5, 5,
	    5, 5, 5, 5, 5, 5, 5
	  ];

	  var groupBases = [
	    0, 0,
	    33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
	    43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
	    16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
	    6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
	    24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
	  ];

	  BN.prototype.toString = function toString (base, padding) {
	    base = base || 10;
	    padding = padding | 0 || 1;

	    var out;
	    if (base === 16 || base === 'hex') {
	      out = '';
	      var off = 0;
	      var carry = 0;
	      for (var i = 0; i < this.length; i++) {
	        var w = this.words[i];
	        var word = (((w << off) | carry) & 0xffffff).toString(16);
	        carry = (w >>> (24 - off)) & 0xffffff;
	        off += 2;
	        if (off >= 26) {
	          off -= 26;
	          i--;
	        }
	        if (carry !== 0 || i !== this.length - 1) {
	          out = zeros[6 - word.length] + word + out;
	        } else {
	          out = word + out;
	        }
	      }
	      if (carry !== 0) {
	        out = carry.toString(16) + out;
	      }
	      while (out.length % padding !== 0) {
	        out = '0' + out;
	      }
	      if (this.negative !== 0) {
	        out = '-' + out;
	      }
	      return out;
	    }

	    if (base === (base | 0) && base >= 2 && base <= 36) {
	      // var groupSize = Math.floor(BN.wordSize * Math.LN2 / Math.log(base));
	      var groupSize = groupSizes[base];
	      // var groupBase = Math.pow(base, groupSize);
	      var groupBase = groupBases[base];
	      out = '';
	      var c = this.clone();
	      c.negative = 0;
	      while (!c.isZero()) {
	        var r = c.modrn(groupBase).toString(base);
	        c = c.idivn(groupBase);

	        if (!c.isZero()) {
	          out = zeros[groupSize - r.length] + r + out;
	        } else {
	          out = r + out;
	        }
	      }
	      if (this.isZero()) {
	        out = '0' + out;
	      }
	      while (out.length % padding !== 0) {
	        out = '0' + out;
	      }
	      if (this.negative !== 0) {
	        out = '-' + out;
	      }
	      return out;
	    }

	    assert(false, 'Base should be between 2 and 36');
	  };

	  BN.prototype.toNumber = function toNumber () {
	    var ret = this.words[0];
	    if (this.length === 2) {
	      ret += this.words[1] * 0x4000000;
	    } else if (this.length === 3 && this.words[2] === 0x01) {
	      // NOTE: at this stage it is known that the top bit is set
	      ret += 0x10000000000000 + (this.words[1] * 0x4000000);
	    } else if (this.length > 2) {
	      assert(false, 'Number can only safely store up to 53 bits');
	    }
	    return (this.negative !== 0) ? -ret : ret;
	  };

	  BN.prototype.toJSON = function toJSON () {
	    return this.toString(16, 2);
	  };

	  if (Buffer) {
	    BN.prototype.toBuffer = function toBuffer (endian, length) {
	      return this.toArrayLike(Buffer, endian, length);
	    };
	  }

	  BN.prototype.toArray = function toArray (endian, length) {
	    return this.toArrayLike(Array, endian, length);
	  };

	  var allocate = function allocate (ArrayType, size) {
	    if (ArrayType.allocUnsafe) {
	      return ArrayType.allocUnsafe(size);
	    }
	    return new ArrayType(size);
	  };

	  BN.prototype.toArrayLike = function toArrayLike (ArrayType, endian, length) {
	    this._strip();

	    var byteLength = this.byteLength();
	    var reqLength = length || Math.max(1, byteLength);
	    assert(byteLength <= reqLength, 'byte array longer than desired length');
	    assert(reqLength > 0, 'Requested array length <= 0');

	    var res = allocate(ArrayType, reqLength);
	    var postfix = endian === 'le' ? 'LE' : 'BE';
	    this['_toArrayLike' + postfix](res, byteLength);
	    return res;
	  };

	  BN.prototype._toArrayLikeLE = function _toArrayLikeLE (res, byteLength) {
	    var position = 0;
	    var carry = 0;

	    for (var i = 0, shift = 0; i < this.length; i++) {
	      var word = (this.words[i] << shift) | carry;

	      res[position++] = word & 0xff;
	      if (position < res.length) {
	        res[position++] = (word >> 8) & 0xff;
	      }
	      if (position < res.length) {
	        res[position++] = (word >> 16) & 0xff;
	      }

	      if (shift === 6) {
	        if (position < res.length) {
	          res[position++] = (word >> 24) & 0xff;
	        }
	        carry = 0;
	        shift = 0;
	      } else {
	        carry = word >>> 24;
	        shift += 2;
	      }
	    }

	    if (position < res.length) {
	      res[position++] = carry;

	      while (position < res.length) {
	        res[position++] = 0;
	      }
	    }
	  };

	  BN.prototype._toArrayLikeBE = function _toArrayLikeBE (res, byteLength) {
	    var position = res.length - 1;
	    var carry = 0;

	    for (var i = 0, shift = 0; i < this.length; i++) {
	      var word = (this.words[i] << shift) | carry;

	      res[position--] = word & 0xff;
	      if (position >= 0) {
	        res[position--] = (word >> 8) & 0xff;
	      }
	      if (position >= 0) {
	        res[position--] = (word >> 16) & 0xff;
	      }

	      if (shift === 6) {
	        if (position >= 0) {
	          res[position--] = (word >> 24) & 0xff;
	        }
	        carry = 0;
	        shift = 0;
	      } else {
	        carry = word >>> 24;
	        shift += 2;
	      }
	    }

	    if (position >= 0) {
	      res[position--] = carry;

	      while (position >= 0) {
	        res[position--] = 0;
	      }
	    }
	  };

	  if (Math.clz32) {
	    BN.prototype._countBits = function _countBits (w) {
	      return 32 - Math.clz32(w);
	    };
	  } else {
	    BN.prototype._countBits = function _countBits (w) {
	      var t = w;
	      var r = 0;
	      if (t >= 0x1000) {
	        r += 13;
	        t >>>= 13;
	      }
	      if (t >= 0x40) {
	        r += 7;
	        t >>>= 7;
	      }
	      if (t >= 0x8) {
	        r += 4;
	        t >>>= 4;
	      }
	      if (t >= 0x02) {
	        r += 2;
	        t >>>= 2;
	      }
	      return r + t;
	    };
	  }

	  BN.prototype._zeroBits = function _zeroBits (w) {
	    // Short-cut
	    if (w === 0) return 26;

	    var t = w;
	    var r = 0;
	    if ((t & 0x1fff) === 0) {
	      r += 13;
	      t >>>= 13;
	    }
	    if ((t & 0x7f) === 0) {
	      r += 7;
	      t >>>= 7;
	    }
	    if ((t & 0xf) === 0) {
	      r += 4;
	      t >>>= 4;
	    }
	    if ((t & 0x3) === 0) {
	      r += 2;
	      t >>>= 2;
	    }
	    if ((t & 0x1) === 0) {
	      r++;
	    }
	    return r;
	  };

	  // Return number of used bits in a BN
	  BN.prototype.bitLength = function bitLength () {
	    var w = this.words[this.length - 1];
	    var hi = this._countBits(w);
	    return (this.length - 1) * 26 + hi;
	  };

	  function toBitArray (num) {
	    var w = new Array(num.bitLength());

	    for (var bit = 0; bit < w.length; bit++) {
	      var off = (bit / 26) | 0;
	      var wbit = bit % 26;

	      w[bit] = (num.words[off] >>> wbit) & 0x01;
	    }

	    return w;
	  }

	  // Number of trailing zero bits
	  BN.prototype.zeroBits = function zeroBits () {
	    if (this.isZero()) return 0;

	    var r = 0;
	    for (var i = 0; i < this.length; i++) {
	      var b = this._zeroBits(this.words[i]);
	      r += b;
	      if (b !== 26) break;
	    }
	    return r;
	  };

	  BN.prototype.byteLength = function byteLength () {
	    return Math.ceil(this.bitLength() / 8);
	  };

	  BN.prototype.toTwos = function toTwos (width) {
	    if (this.negative !== 0) {
	      return this.abs().inotn(width).iaddn(1);
	    }
	    return this.clone();
	  };

	  BN.prototype.fromTwos = function fromTwos (width) {
	    if (this.testn(width - 1)) {
	      return this.notn(width).iaddn(1).ineg();
	    }
	    return this.clone();
	  };

	  BN.prototype.isNeg = function isNeg () {
	    return this.negative !== 0;
	  };

	  // Return negative clone of `this`
	  BN.prototype.neg = function neg () {
	    return this.clone().ineg();
	  };

	  BN.prototype.ineg = function ineg () {
	    if (!this.isZero()) {
	      this.negative ^= 1;
	    }

	    return this;
	  };

	  // Or `num` with `this` in-place
	  BN.prototype.iuor = function iuor (num) {
	    while (this.length < num.length) {
	      this.words[this.length++] = 0;
	    }

	    for (var i = 0; i < num.length; i++) {
	      this.words[i] = this.words[i] | num.words[i];
	    }

	    return this._strip();
	  };

	  BN.prototype.ior = function ior (num) {
	    assert((this.negative | num.negative) === 0);
	    return this.iuor(num);
	  };

	  // Or `num` with `this`
	  BN.prototype.or = function or (num) {
	    if (this.length > num.length) return this.clone().ior(num);
	    return num.clone().ior(this);
	  };

	  BN.prototype.uor = function uor (num) {
	    if (this.length > num.length) return this.clone().iuor(num);
	    return num.clone().iuor(this);
	  };

	  // And `num` with `this` in-place
	  BN.prototype.iuand = function iuand (num) {
	    // b = min-length(num, this)
	    var b;
	    if (this.length > num.length) {
	      b = num;
	    } else {
	      b = this;
	    }

	    for (var i = 0; i < b.length; i++) {
	      this.words[i] = this.words[i] & num.words[i];
	    }

	    this.length = b.length;

	    return this._strip();
	  };

	  BN.prototype.iand = function iand (num) {
	    assert((this.negative | num.negative) === 0);
	    return this.iuand(num);
	  };

	  // And `num` with `this`
	  BN.prototype.and = function and (num) {
	    if (this.length > num.length) return this.clone().iand(num);
	    return num.clone().iand(this);
	  };

	  BN.prototype.uand = function uand (num) {
	    if (this.length > num.length) return this.clone().iuand(num);
	    return num.clone().iuand(this);
	  };

	  // Xor `num` with `this` in-place
	  BN.prototype.iuxor = function iuxor (num) {
	    // a.length > b.length
	    var a;
	    var b;
	    if (this.length > num.length) {
	      a = this;
	      b = num;
	    } else {
	      a = num;
	      b = this;
	    }

	    for (var i = 0; i < b.length; i++) {
	      this.words[i] = a.words[i] ^ b.words[i];
	    }

	    if (this !== a) {
	      for (; i < a.length; i++) {
	        this.words[i] = a.words[i];
	      }
	    }

	    this.length = a.length;

	    return this._strip();
	  };

	  BN.prototype.ixor = function ixor (num) {
	    assert((this.negative | num.negative) === 0);
	    return this.iuxor(num);
	  };

	  // Xor `num` with `this`
	  BN.prototype.xor = function xor (num) {
	    if (this.length > num.length) return this.clone().ixor(num);
	    return num.clone().ixor(this);
	  };

	  BN.prototype.uxor = function uxor (num) {
	    if (this.length > num.length) return this.clone().iuxor(num);
	    return num.clone().iuxor(this);
	  };

	  // Not ``this`` with ``width`` bitwidth
	  BN.prototype.inotn = function inotn (width) {
	    assert(typeof width === 'number' && width >= 0);

	    var bytesNeeded = Math.ceil(width / 26) | 0;
	    var bitsLeft = width % 26;

	    // Extend the buffer with leading zeroes
	    this._expand(bytesNeeded);

	    if (bitsLeft > 0) {
	      bytesNeeded--;
	    }

	    // Handle complete words
	    for (var i = 0; i < bytesNeeded; i++) {
	      this.words[i] = ~this.words[i] & 0x3ffffff;
	    }

	    // Handle the residue
	    if (bitsLeft > 0) {
	      this.words[i] = ~this.words[i] & (0x3ffffff >> (26 - bitsLeft));
	    }

	    // And remove leading zeroes
	    return this._strip();
	  };

	  BN.prototype.notn = function notn (width) {
	    return this.clone().inotn(width);
	  };

	  // Set `bit` of `this`
	  BN.prototype.setn = function setn (bit, val) {
	    assert(typeof bit === 'number' && bit >= 0);

	    var off = (bit / 26) | 0;
	    var wbit = bit % 26;

	    this._expand(off + 1);

	    if (val) {
	      this.words[off] = this.words[off] | (1 << wbit);
	    } else {
	      this.words[off] = this.words[off] & ~(1 << wbit);
	    }

	    return this._strip();
	  };

	  // Add `num` to `this` in-place
	  BN.prototype.iadd = function iadd (num) {
	    var r;

	    // negative + positive
	    if (this.negative !== 0 && num.negative === 0) {
	      this.negative = 0;
	      r = this.isub(num);
	      this.negative ^= 1;
	      return this._normSign();

	    // positive + negative
	    } else if (this.negative === 0 && num.negative !== 0) {
	      num.negative = 0;
	      r = this.isub(num);
	      num.negative = 1;
	      return r._normSign();
	    }

	    // a.length > b.length
	    var a, b;
	    if (this.length > num.length) {
	      a = this;
	      b = num;
	    } else {
	      a = num;
	      b = this;
	    }

	    var carry = 0;
	    for (var i = 0; i < b.length; i++) {
	      r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
	      this.words[i] = r & 0x3ffffff;
	      carry = r >>> 26;
	    }
	    for (; carry !== 0 && i < a.length; i++) {
	      r = (a.words[i] | 0) + carry;
	      this.words[i] = r & 0x3ffffff;
	      carry = r >>> 26;
	    }

	    this.length = a.length;
	    if (carry !== 0) {
	      this.words[this.length] = carry;
	      this.length++;
	    // Copy the rest of the words
	    } else if (a !== this) {
	      for (; i < a.length; i++) {
	        this.words[i] = a.words[i];
	      }
	    }

	    return this;
	  };

	  // Add `num` to `this`
	  BN.prototype.add = function add (num) {
	    var res;
	    if (num.negative !== 0 && this.negative === 0) {
	      num.negative = 0;
	      res = this.sub(num);
	      num.negative ^= 1;
	      return res;
	    } else if (num.negative === 0 && this.negative !== 0) {
	      this.negative = 0;
	      res = num.sub(this);
	      this.negative = 1;
	      return res;
	    }

	    if (this.length > num.length) return this.clone().iadd(num);

	    return num.clone().iadd(this);
	  };

	  // Subtract `num` from `this` in-place
	  BN.prototype.isub = function isub (num) {
	    // this - (-num) = this + num
	    if (num.negative !== 0) {
	      num.negative = 0;
	      var r = this.iadd(num);
	      num.negative = 1;
	      return r._normSign();

	    // -this - num = -(this + num)
	    } else if (this.negative !== 0) {
	      this.negative = 0;
	      this.iadd(num);
	      this.negative = 1;
	      return this._normSign();
	    }

	    // At this point both numbers are positive
	    var cmp = this.cmp(num);

	    // Optimization - zeroify
	    if (cmp === 0) {
	      this.negative = 0;
	      this.length = 1;
	      this.words[0] = 0;
	      return this;
	    }

	    // a > b
	    var a, b;
	    if (cmp > 0) {
	      a = this;
	      b = num;
	    } else {
	      a = num;
	      b = this;
	    }

	    var carry = 0;
	    for (var i = 0; i < b.length; i++) {
	      r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
	      carry = r >> 26;
	      this.words[i] = r & 0x3ffffff;
	    }
	    for (; carry !== 0 && i < a.length; i++) {
	      r = (a.words[i] | 0) + carry;
	      carry = r >> 26;
	      this.words[i] = r & 0x3ffffff;
	    }

	    // Copy rest of the words
	    if (carry === 0 && i < a.length && a !== this) {
	      for (; i < a.length; i++) {
	        this.words[i] = a.words[i];
	      }
	    }

	    this.length = Math.max(this.length, i);

	    if (a !== this) {
	      this.negative = 1;
	    }

	    return this._strip();
	  };

	  // Subtract `num` from `this`
	  BN.prototype.sub = function sub (num) {
	    return this.clone().isub(num);
	  };

	  function smallMulTo (self, num, out) {
	    out.negative = num.negative ^ self.negative;
	    var len = (self.length + num.length) | 0;
	    out.length = len;
	    len = (len - 1) | 0;

	    // Peel one iteration (compiler can't do it, because of code complexity)
	    var a = self.words[0] | 0;
	    var b = num.words[0] | 0;
	    var r = a * b;

	    var lo = r & 0x3ffffff;
	    var carry = (r / 0x4000000) | 0;
	    out.words[0] = lo;

	    for (var k = 1; k < len; k++) {
	      // Sum all words with the same `i + j = k` and accumulate `ncarry`,
	      // note that ncarry could be >= 0x3ffffff
	      var ncarry = carry >>> 26;
	      var rword = carry & 0x3ffffff;
	      var maxJ = Math.min(k, num.length - 1);
	      for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
	        var i = (k - j) | 0;
	        a = self.words[i] | 0;
	        b = num.words[j] | 0;
	        r = a * b + rword;
	        ncarry += (r / 0x4000000) | 0;
	        rword = r & 0x3ffffff;
	      }
	      out.words[k] = rword | 0;
	      carry = ncarry | 0;
	    }
	    if (carry !== 0) {
	      out.words[k] = carry | 0;
	    } else {
	      out.length--;
	    }

	    return out._strip();
	  }

	  // TODO(indutny): it may be reasonable to omit it for users who don't need
	  // to work with 256-bit numbers, otherwise it gives 20% improvement for 256-bit
	  // multiplication (like elliptic secp256k1).
	  var comb10MulTo = function comb10MulTo (self, num, out) {
	    var a = self.words;
	    var b = num.words;
	    var o = out.words;
	    var c = 0;
	    var lo;
	    var mid;
	    var hi;
	    var a0 = a[0] | 0;
	    var al0 = a0 & 0x1fff;
	    var ah0 = a0 >>> 13;
	    var a1 = a[1] | 0;
	    var al1 = a1 & 0x1fff;
	    var ah1 = a1 >>> 13;
	    var a2 = a[2] | 0;
	    var al2 = a2 & 0x1fff;
	    var ah2 = a2 >>> 13;
	    var a3 = a[3] | 0;
	    var al3 = a3 & 0x1fff;
	    var ah3 = a3 >>> 13;
	    var a4 = a[4] | 0;
	    var al4 = a4 & 0x1fff;
	    var ah4 = a4 >>> 13;
	    var a5 = a[5] | 0;
	    var al5 = a5 & 0x1fff;
	    var ah5 = a5 >>> 13;
	    var a6 = a[6] | 0;
	    var al6 = a6 & 0x1fff;
	    var ah6 = a6 >>> 13;
	    var a7 = a[7] | 0;
	    var al7 = a7 & 0x1fff;
	    var ah7 = a7 >>> 13;
	    var a8 = a[8] | 0;
	    var al8 = a8 & 0x1fff;
	    var ah8 = a8 >>> 13;
	    var a9 = a[9] | 0;
	    var al9 = a9 & 0x1fff;
	    var ah9 = a9 >>> 13;
	    var b0 = b[0] | 0;
	    var bl0 = b0 & 0x1fff;
	    var bh0 = b0 >>> 13;
	    var b1 = b[1] | 0;
	    var bl1 = b1 & 0x1fff;
	    var bh1 = b1 >>> 13;
	    var b2 = b[2] | 0;
	    var bl2 = b2 & 0x1fff;
	    var bh2 = b2 >>> 13;
	    var b3 = b[3] | 0;
	    var bl3 = b3 & 0x1fff;
	    var bh3 = b3 >>> 13;
	    var b4 = b[4] | 0;
	    var bl4 = b4 & 0x1fff;
	    var bh4 = b4 >>> 13;
	    var b5 = b[5] | 0;
	    var bl5 = b5 & 0x1fff;
	    var bh5 = b5 >>> 13;
	    var b6 = b[6] | 0;
	    var bl6 = b6 & 0x1fff;
	    var bh6 = b6 >>> 13;
	    var b7 = b[7] | 0;
	    var bl7 = b7 & 0x1fff;
	    var bh7 = b7 >>> 13;
	    var b8 = b[8] | 0;
	    var bl8 = b8 & 0x1fff;
	    var bh8 = b8 >>> 13;
	    var b9 = b[9] | 0;
	    var bl9 = b9 & 0x1fff;
	    var bh9 = b9 >>> 13;

	    out.negative = self.negative ^ num.negative;
	    out.length = 19;
	    /* k = 0 */
	    lo = Math.imul(al0, bl0);
	    mid = Math.imul(al0, bh0);
	    mid = (mid + Math.imul(ah0, bl0)) | 0;
	    hi = Math.imul(ah0, bh0);
	    var w0 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w0 >>> 26)) | 0;
	    w0 &= 0x3ffffff;
	    /* k = 1 */
	    lo = Math.imul(al1, bl0);
	    mid = Math.imul(al1, bh0);
	    mid = (mid + Math.imul(ah1, bl0)) | 0;
	    hi = Math.imul(ah1, bh0);
	    lo = (lo + Math.imul(al0, bl1)) | 0;
	    mid = (mid + Math.imul(al0, bh1)) | 0;
	    mid = (mid + Math.imul(ah0, bl1)) | 0;
	    hi = (hi + Math.imul(ah0, bh1)) | 0;
	    var w1 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w1 >>> 26)) | 0;
	    w1 &= 0x3ffffff;
	    /* k = 2 */
	    lo = Math.imul(al2, bl0);
	    mid = Math.imul(al2, bh0);
	    mid = (mid + Math.imul(ah2, bl0)) | 0;
	    hi = Math.imul(ah2, bh0);
	    lo = (lo + Math.imul(al1, bl1)) | 0;
	    mid = (mid + Math.imul(al1, bh1)) | 0;
	    mid = (mid + Math.imul(ah1, bl1)) | 0;
	    hi = (hi + Math.imul(ah1, bh1)) | 0;
	    lo = (lo + Math.imul(al0, bl2)) | 0;
	    mid = (mid + Math.imul(al0, bh2)) | 0;
	    mid = (mid + Math.imul(ah0, bl2)) | 0;
	    hi = (hi + Math.imul(ah0, bh2)) | 0;
	    var w2 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w2 >>> 26)) | 0;
	    w2 &= 0x3ffffff;
	    /* k = 3 */
	    lo = Math.imul(al3, bl0);
	    mid = Math.imul(al3, bh0);
	    mid = (mid + Math.imul(ah3, bl0)) | 0;
	    hi = Math.imul(ah3, bh0);
	    lo = (lo + Math.imul(al2, bl1)) | 0;
	    mid = (mid + Math.imul(al2, bh1)) | 0;
	    mid = (mid + Math.imul(ah2, bl1)) | 0;
	    hi = (hi + Math.imul(ah2, bh1)) | 0;
	    lo = (lo + Math.imul(al1, bl2)) | 0;
	    mid = (mid + Math.imul(al1, bh2)) | 0;
	    mid = (mid + Math.imul(ah1, bl2)) | 0;
	    hi = (hi + Math.imul(ah1, bh2)) | 0;
	    lo = (lo + Math.imul(al0, bl3)) | 0;
	    mid = (mid + Math.imul(al0, bh3)) | 0;
	    mid = (mid + Math.imul(ah0, bl3)) | 0;
	    hi = (hi + Math.imul(ah0, bh3)) | 0;
	    var w3 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w3 >>> 26)) | 0;
	    w3 &= 0x3ffffff;
	    /* k = 4 */
	    lo = Math.imul(al4, bl0);
	    mid = Math.imul(al4, bh0);
	    mid = (mid + Math.imul(ah4, bl0)) | 0;
	    hi = Math.imul(ah4, bh0);
	    lo = (lo + Math.imul(al3, bl1)) | 0;
	    mid = (mid + Math.imul(al3, bh1)) | 0;
	    mid = (mid + Math.imul(ah3, bl1)) | 0;
	    hi = (hi + Math.imul(ah3, bh1)) | 0;
	    lo = (lo + Math.imul(al2, bl2)) | 0;
	    mid = (mid + Math.imul(al2, bh2)) | 0;
	    mid = (mid + Math.imul(ah2, bl2)) | 0;
	    hi = (hi + Math.imul(ah2, bh2)) | 0;
	    lo = (lo + Math.imul(al1, bl3)) | 0;
	    mid = (mid + Math.imul(al1, bh3)) | 0;
	    mid = (mid + Math.imul(ah1, bl3)) | 0;
	    hi = (hi + Math.imul(ah1, bh3)) | 0;
	    lo = (lo + Math.imul(al0, bl4)) | 0;
	    mid = (mid + Math.imul(al0, bh4)) | 0;
	    mid = (mid + Math.imul(ah0, bl4)) | 0;
	    hi = (hi + Math.imul(ah0, bh4)) | 0;
	    var w4 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w4 >>> 26)) | 0;
	    w4 &= 0x3ffffff;
	    /* k = 5 */
	    lo = Math.imul(al5, bl0);
	    mid = Math.imul(al5, bh0);
	    mid = (mid + Math.imul(ah5, bl0)) | 0;
	    hi = Math.imul(ah5, bh0);
	    lo = (lo + Math.imul(al4, bl1)) | 0;
	    mid = (mid + Math.imul(al4, bh1)) | 0;
	    mid = (mid + Math.imul(ah4, bl1)) | 0;
	    hi = (hi + Math.imul(ah4, bh1)) | 0;
	    lo = (lo + Math.imul(al3, bl2)) | 0;
	    mid = (mid + Math.imul(al3, bh2)) | 0;
	    mid = (mid + Math.imul(ah3, bl2)) | 0;
	    hi = (hi + Math.imul(ah3, bh2)) | 0;
	    lo = (lo + Math.imul(al2, bl3)) | 0;
	    mid = (mid + Math.imul(al2, bh3)) | 0;
	    mid = (mid + Math.imul(ah2, bl3)) | 0;
	    hi = (hi + Math.imul(ah2, bh3)) | 0;
	    lo = (lo + Math.imul(al1, bl4)) | 0;
	    mid = (mid + Math.imul(al1, bh4)) | 0;
	    mid = (mid + Math.imul(ah1, bl4)) | 0;
	    hi = (hi + Math.imul(ah1, bh4)) | 0;
	    lo = (lo + Math.imul(al0, bl5)) | 0;
	    mid = (mid + Math.imul(al0, bh5)) | 0;
	    mid = (mid + Math.imul(ah0, bl5)) | 0;
	    hi = (hi + Math.imul(ah0, bh5)) | 0;
	    var w5 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w5 >>> 26)) | 0;
	    w5 &= 0x3ffffff;
	    /* k = 6 */
	    lo = Math.imul(al6, bl0);
	    mid = Math.imul(al6, bh0);
	    mid = (mid + Math.imul(ah6, bl0)) | 0;
	    hi = Math.imul(ah6, bh0);
	    lo = (lo + Math.imul(al5, bl1)) | 0;
	    mid = (mid + Math.imul(al5, bh1)) | 0;
	    mid = (mid + Math.imul(ah5, bl1)) | 0;
	    hi = (hi + Math.imul(ah5, bh1)) | 0;
	    lo = (lo + Math.imul(al4, bl2)) | 0;
	    mid = (mid + Math.imul(al4, bh2)) | 0;
	    mid = (mid + Math.imul(ah4, bl2)) | 0;
	    hi = (hi + Math.imul(ah4, bh2)) | 0;
	    lo = (lo + Math.imul(al3, bl3)) | 0;
	    mid = (mid + Math.imul(al3, bh3)) | 0;
	    mid = (mid + Math.imul(ah3, bl3)) | 0;
	    hi = (hi + Math.imul(ah3, bh3)) | 0;
	    lo = (lo + Math.imul(al2, bl4)) | 0;
	    mid = (mid + Math.imul(al2, bh4)) | 0;
	    mid = (mid + Math.imul(ah2, bl4)) | 0;
	    hi = (hi + Math.imul(ah2, bh4)) | 0;
	    lo = (lo + Math.imul(al1, bl5)) | 0;
	    mid = (mid + Math.imul(al1, bh5)) | 0;
	    mid = (mid + Math.imul(ah1, bl5)) | 0;
	    hi = (hi + Math.imul(ah1, bh5)) | 0;
	    lo = (lo + Math.imul(al0, bl6)) | 0;
	    mid = (mid + Math.imul(al0, bh6)) | 0;
	    mid = (mid + Math.imul(ah0, bl6)) | 0;
	    hi = (hi + Math.imul(ah0, bh6)) | 0;
	    var w6 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w6 >>> 26)) | 0;
	    w6 &= 0x3ffffff;
	    /* k = 7 */
	    lo = Math.imul(al7, bl0);
	    mid = Math.imul(al7, bh0);
	    mid = (mid + Math.imul(ah7, bl0)) | 0;
	    hi = Math.imul(ah7, bh0);
	    lo = (lo + Math.imul(al6, bl1)) | 0;
	    mid = (mid + Math.imul(al6, bh1)) | 0;
	    mid = (mid + Math.imul(ah6, bl1)) | 0;
	    hi = (hi + Math.imul(ah6, bh1)) | 0;
	    lo = (lo + Math.imul(al5, bl2)) | 0;
	    mid = (mid + Math.imul(al5, bh2)) | 0;
	    mid = (mid + Math.imul(ah5, bl2)) | 0;
	    hi = (hi + Math.imul(ah5, bh2)) | 0;
	    lo = (lo + Math.imul(al4, bl3)) | 0;
	    mid = (mid + Math.imul(al4, bh3)) | 0;
	    mid = (mid + Math.imul(ah4, bl3)) | 0;
	    hi = (hi + Math.imul(ah4, bh3)) | 0;
	    lo = (lo + Math.imul(al3, bl4)) | 0;
	    mid = (mid + Math.imul(al3, bh4)) | 0;
	    mid = (mid + Math.imul(ah3, bl4)) | 0;
	    hi = (hi + Math.imul(ah3, bh4)) | 0;
	    lo = (lo + Math.imul(al2, bl5)) | 0;
	    mid = (mid + Math.imul(al2, bh5)) | 0;
	    mid = (mid + Math.imul(ah2, bl5)) | 0;
	    hi = (hi + Math.imul(ah2, bh5)) | 0;
	    lo = (lo + Math.imul(al1, bl6)) | 0;
	    mid = (mid + Math.imul(al1, bh6)) | 0;
	    mid = (mid + Math.imul(ah1, bl6)) | 0;
	    hi = (hi + Math.imul(ah1, bh6)) | 0;
	    lo = (lo + Math.imul(al0, bl7)) | 0;
	    mid = (mid + Math.imul(al0, bh7)) | 0;
	    mid = (mid + Math.imul(ah0, bl7)) | 0;
	    hi = (hi + Math.imul(ah0, bh7)) | 0;
	    var w7 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w7 >>> 26)) | 0;
	    w7 &= 0x3ffffff;
	    /* k = 8 */
	    lo = Math.imul(al8, bl0);
	    mid = Math.imul(al8, bh0);
	    mid = (mid + Math.imul(ah8, bl0)) | 0;
	    hi = Math.imul(ah8, bh0);
	    lo = (lo + Math.imul(al7, bl1)) | 0;
	    mid = (mid + Math.imul(al7, bh1)) | 0;
	    mid = (mid + Math.imul(ah7, bl1)) | 0;
	    hi = (hi + Math.imul(ah7, bh1)) | 0;
	    lo = (lo + Math.imul(al6, bl2)) | 0;
	    mid = (mid + Math.imul(al6, bh2)) | 0;
	    mid = (mid + Math.imul(ah6, bl2)) | 0;
	    hi = (hi + Math.imul(ah6, bh2)) | 0;
	    lo = (lo + Math.imul(al5, bl3)) | 0;
	    mid = (mid + Math.imul(al5, bh3)) | 0;
	    mid = (mid + Math.imul(ah5, bl3)) | 0;
	    hi = (hi + Math.imul(ah5, bh3)) | 0;
	    lo = (lo + Math.imul(al4, bl4)) | 0;
	    mid = (mid + Math.imul(al4, bh4)) | 0;
	    mid = (mid + Math.imul(ah4, bl4)) | 0;
	    hi = (hi + Math.imul(ah4, bh4)) | 0;
	    lo = (lo + Math.imul(al3, bl5)) | 0;
	    mid = (mid + Math.imul(al3, bh5)) | 0;
	    mid = (mid + Math.imul(ah3, bl5)) | 0;
	    hi = (hi + Math.imul(ah3, bh5)) | 0;
	    lo = (lo + Math.imul(al2, bl6)) | 0;
	    mid = (mid + Math.imul(al2, bh6)) | 0;
	    mid = (mid + Math.imul(ah2, bl6)) | 0;
	    hi = (hi + Math.imul(ah2, bh6)) | 0;
	    lo = (lo + Math.imul(al1, bl7)) | 0;
	    mid = (mid + Math.imul(al1, bh7)) | 0;
	    mid = (mid + Math.imul(ah1, bl7)) | 0;
	    hi = (hi + Math.imul(ah1, bh7)) | 0;
	    lo = (lo + Math.imul(al0, bl8)) | 0;
	    mid = (mid + Math.imul(al0, bh8)) | 0;
	    mid = (mid + Math.imul(ah0, bl8)) | 0;
	    hi = (hi + Math.imul(ah0, bh8)) | 0;
	    var w8 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w8 >>> 26)) | 0;
	    w8 &= 0x3ffffff;
	    /* k = 9 */
	    lo = Math.imul(al9, bl0);
	    mid = Math.imul(al9, bh0);
	    mid = (mid + Math.imul(ah9, bl0)) | 0;
	    hi = Math.imul(ah9, bh0);
	    lo = (lo + Math.imul(al8, bl1)) | 0;
	    mid = (mid + Math.imul(al8, bh1)) | 0;
	    mid = (mid + Math.imul(ah8, bl1)) | 0;
	    hi = (hi + Math.imul(ah8, bh1)) | 0;
	    lo = (lo + Math.imul(al7, bl2)) | 0;
	    mid = (mid + Math.imul(al7, bh2)) | 0;
	    mid = (mid + Math.imul(ah7, bl2)) | 0;
	    hi = (hi + Math.imul(ah7, bh2)) | 0;
	    lo = (lo + Math.imul(al6, bl3)) | 0;
	    mid = (mid + Math.imul(al6, bh3)) | 0;
	    mid = (mid + Math.imul(ah6, bl3)) | 0;
	    hi = (hi + Math.imul(ah6, bh3)) | 0;
	    lo = (lo + Math.imul(al5, bl4)) | 0;
	    mid = (mid + Math.imul(al5, bh4)) | 0;
	    mid = (mid + Math.imul(ah5, bl4)) | 0;
	    hi = (hi + Math.imul(ah5, bh4)) | 0;
	    lo = (lo + Math.imul(al4, bl5)) | 0;
	    mid = (mid + Math.imul(al4, bh5)) | 0;
	    mid = (mid + Math.imul(ah4, bl5)) | 0;
	    hi = (hi + Math.imul(ah4, bh5)) | 0;
	    lo = (lo + Math.imul(al3, bl6)) | 0;
	    mid = (mid + Math.imul(al3, bh6)) | 0;
	    mid = (mid + Math.imul(ah3, bl6)) | 0;
	    hi = (hi + Math.imul(ah3, bh6)) | 0;
	    lo = (lo + Math.imul(al2, bl7)) | 0;
	    mid = (mid + Math.imul(al2, bh7)) | 0;
	    mid = (mid + Math.imul(ah2, bl7)) | 0;
	    hi = (hi + Math.imul(ah2, bh7)) | 0;
	    lo = (lo + Math.imul(al1, bl8)) | 0;
	    mid = (mid + Math.imul(al1, bh8)) | 0;
	    mid = (mid + Math.imul(ah1, bl8)) | 0;
	    hi = (hi + Math.imul(ah1, bh8)) | 0;
	    lo = (lo + Math.imul(al0, bl9)) | 0;
	    mid = (mid + Math.imul(al0, bh9)) | 0;
	    mid = (mid + Math.imul(ah0, bl9)) | 0;
	    hi = (hi + Math.imul(ah0, bh9)) | 0;
	    var w9 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w9 >>> 26)) | 0;
	    w9 &= 0x3ffffff;
	    /* k = 10 */
	    lo = Math.imul(al9, bl1);
	    mid = Math.imul(al9, bh1);
	    mid = (mid + Math.imul(ah9, bl1)) | 0;
	    hi = Math.imul(ah9, bh1);
	    lo = (lo + Math.imul(al8, bl2)) | 0;
	    mid = (mid + Math.imul(al8, bh2)) | 0;
	    mid = (mid + Math.imul(ah8, bl2)) | 0;
	    hi = (hi + Math.imul(ah8, bh2)) | 0;
	    lo = (lo + Math.imul(al7, bl3)) | 0;
	    mid = (mid + Math.imul(al7, bh3)) | 0;
	    mid = (mid + Math.imul(ah7, bl3)) | 0;
	    hi = (hi + Math.imul(ah7, bh3)) | 0;
	    lo = (lo + Math.imul(al6, bl4)) | 0;
	    mid = (mid + Math.imul(al6, bh4)) | 0;
	    mid = (mid + Math.imul(ah6, bl4)) | 0;
	    hi = (hi + Math.imul(ah6, bh4)) | 0;
	    lo = (lo + Math.imul(al5, bl5)) | 0;
	    mid = (mid + Math.imul(al5, bh5)) | 0;
	    mid = (mid + Math.imul(ah5, bl5)) | 0;
	    hi = (hi + Math.imul(ah5, bh5)) | 0;
	    lo = (lo + Math.imul(al4, bl6)) | 0;
	    mid = (mid + Math.imul(al4, bh6)) | 0;
	    mid = (mid + Math.imul(ah4, bl6)) | 0;
	    hi = (hi + Math.imul(ah4, bh6)) | 0;
	    lo = (lo + Math.imul(al3, bl7)) | 0;
	    mid = (mid + Math.imul(al3, bh7)) | 0;
	    mid = (mid + Math.imul(ah3, bl7)) | 0;
	    hi = (hi + Math.imul(ah3, bh7)) | 0;
	    lo = (lo + Math.imul(al2, bl8)) | 0;
	    mid = (mid + Math.imul(al2, bh8)) | 0;
	    mid = (mid + Math.imul(ah2, bl8)) | 0;
	    hi = (hi + Math.imul(ah2, bh8)) | 0;
	    lo = (lo + Math.imul(al1, bl9)) | 0;
	    mid = (mid + Math.imul(al1, bh9)) | 0;
	    mid = (mid + Math.imul(ah1, bl9)) | 0;
	    hi = (hi + Math.imul(ah1, bh9)) | 0;
	    var w10 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w10 >>> 26)) | 0;
	    w10 &= 0x3ffffff;
	    /* k = 11 */
	    lo = Math.imul(al9, bl2);
	    mid = Math.imul(al9, bh2);
	    mid = (mid + Math.imul(ah9, bl2)) | 0;
	    hi = Math.imul(ah9, bh2);
	    lo = (lo + Math.imul(al8, bl3)) | 0;
	    mid = (mid + Math.imul(al8, bh3)) | 0;
	    mid = (mid + Math.imul(ah8, bl3)) | 0;
	    hi = (hi + Math.imul(ah8, bh3)) | 0;
	    lo = (lo + Math.imul(al7, bl4)) | 0;
	    mid = (mid + Math.imul(al7, bh4)) | 0;
	    mid = (mid + Math.imul(ah7, bl4)) | 0;
	    hi = (hi + Math.imul(ah7, bh4)) | 0;
	    lo = (lo + Math.imul(al6, bl5)) | 0;
	    mid = (mid + Math.imul(al6, bh5)) | 0;
	    mid = (mid + Math.imul(ah6, bl5)) | 0;
	    hi = (hi + Math.imul(ah6, bh5)) | 0;
	    lo = (lo + Math.imul(al5, bl6)) | 0;
	    mid = (mid + Math.imul(al5, bh6)) | 0;
	    mid = (mid + Math.imul(ah5, bl6)) | 0;
	    hi = (hi + Math.imul(ah5, bh6)) | 0;
	    lo = (lo + Math.imul(al4, bl7)) | 0;
	    mid = (mid + Math.imul(al4, bh7)) | 0;
	    mid = (mid + Math.imul(ah4, bl7)) | 0;
	    hi = (hi + Math.imul(ah4, bh7)) | 0;
	    lo = (lo + Math.imul(al3, bl8)) | 0;
	    mid = (mid + Math.imul(al3, bh8)) | 0;
	    mid = (mid + Math.imul(ah3, bl8)) | 0;
	    hi = (hi + Math.imul(ah3, bh8)) | 0;
	    lo = (lo + Math.imul(al2, bl9)) | 0;
	    mid = (mid + Math.imul(al2, bh9)) | 0;
	    mid = (mid + Math.imul(ah2, bl9)) | 0;
	    hi = (hi + Math.imul(ah2, bh9)) | 0;
	    var w11 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w11 >>> 26)) | 0;
	    w11 &= 0x3ffffff;
	    /* k = 12 */
	    lo = Math.imul(al9, bl3);
	    mid = Math.imul(al9, bh3);
	    mid = (mid + Math.imul(ah9, bl3)) | 0;
	    hi = Math.imul(ah9, bh3);
	    lo = (lo + Math.imul(al8, bl4)) | 0;
	    mid = (mid + Math.imul(al8, bh4)) | 0;
	    mid = (mid + Math.imul(ah8, bl4)) | 0;
	    hi = (hi + Math.imul(ah8, bh4)) | 0;
	    lo = (lo + Math.imul(al7, bl5)) | 0;
	    mid = (mid + Math.imul(al7, bh5)) | 0;
	    mid = (mid + Math.imul(ah7, bl5)) | 0;
	    hi = (hi + Math.imul(ah7, bh5)) | 0;
	    lo = (lo + Math.imul(al6, bl6)) | 0;
	    mid = (mid + Math.imul(al6, bh6)) | 0;
	    mid = (mid + Math.imul(ah6, bl6)) | 0;
	    hi = (hi + Math.imul(ah6, bh6)) | 0;
	    lo = (lo + Math.imul(al5, bl7)) | 0;
	    mid = (mid + Math.imul(al5, bh7)) | 0;
	    mid = (mid + Math.imul(ah5, bl7)) | 0;
	    hi = (hi + Math.imul(ah5, bh7)) | 0;
	    lo = (lo + Math.imul(al4, bl8)) | 0;
	    mid = (mid + Math.imul(al4, bh8)) | 0;
	    mid = (mid + Math.imul(ah4, bl8)) | 0;
	    hi = (hi + Math.imul(ah4, bh8)) | 0;
	    lo = (lo + Math.imul(al3, bl9)) | 0;
	    mid = (mid + Math.imul(al3, bh9)) | 0;
	    mid = (mid + Math.imul(ah3, bl9)) | 0;
	    hi = (hi + Math.imul(ah3, bh9)) | 0;
	    var w12 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w12 >>> 26)) | 0;
	    w12 &= 0x3ffffff;
	    /* k = 13 */
	    lo = Math.imul(al9, bl4);
	    mid = Math.imul(al9, bh4);
	    mid = (mid + Math.imul(ah9, bl4)) | 0;
	    hi = Math.imul(ah9, bh4);
	    lo = (lo + Math.imul(al8, bl5)) | 0;
	    mid = (mid + Math.imul(al8, bh5)) | 0;
	    mid = (mid + Math.imul(ah8, bl5)) | 0;
	    hi = (hi + Math.imul(ah8, bh5)) | 0;
	    lo = (lo + Math.imul(al7, bl6)) | 0;
	    mid = (mid + Math.imul(al7, bh6)) | 0;
	    mid = (mid + Math.imul(ah7, bl6)) | 0;
	    hi = (hi + Math.imul(ah7, bh6)) | 0;
	    lo = (lo + Math.imul(al6, bl7)) | 0;
	    mid = (mid + Math.imul(al6, bh7)) | 0;
	    mid = (mid + Math.imul(ah6, bl7)) | 0;
	    hi = (hi + Math.imul(ah6, bh7)) | 0;
	    lo = (lo + Math.imul(al5, bl8)) | 0;
	    mid = (mid + Math.imul(al5, bh8)) | 0;
	    mid = (mid + Math.imul(ah5, bl8)) | 0;
	    hi = (hi + Math.imul(ah5, bh8)) | 0;
	    lo = (lo + Math.imul(al4, bl9)) | 0;
	    mid = (mid + Math.imul(al4, bh9)) | 0;
	    mid = (mid + Math.imul(ah4, bl9)) | 0;
	    hi = (hi + Math.imul(ah4, bh9)) | 0;
	    var w13 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w13 >>> 26)) | 0;
	    w13 &= 0x3ffffff;
	    /* k = 14 */
	    lo = Math.imul(al9, bl5);
	    mid = Math.imul(al9, bh5);
	    mid = (mid + Math.imul(ah9, bl5)) | 0;
	    hi = Math.imul(ah9, bh5);
	    lo = (lo + Math.imul(al8, bl6)) | 0;
	    mid = (mid + Math.imul(al8, bh6)) | 0;
	    mid = (mid + Math.imul(ah8, bl6)) | 0;
	    hi = (hi + Math.imul(ah8, bh6)) | 0;
	    lo = (lo + Math.imul(al7, bl7)) | 0;
	    mid = (mid + Math.imul(al7, bh7)) | 0;
	    mid = (mid + Math.imul(ah7, bl7)) | 0;
	    hi = (hi + Math.imul(ah7, bh7)) | 0;
	    lo = (lo + Math.imul(al6, bl8)) | 0;
	    mid = (mid + Math.imul(al6, bh8)) | 0;
	    mid = (mid + Math.imul(ah6, bl8)) | 0;
	    hi = (hi + Math.imul(ah6, bh8)) | 0;
	    lo = (lo + Math.imul(al5, bl9)) | 0;
	    mid = (mid + Math.imul(al5, bh9)) | 0;
	    mid = (mid + Math.imul(ah5, bl9)) | 0;
	    hi = (hi + Math.imul(ah5, bh9)) | 0;
	    var w14 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w14 >>> 26)) | 0;
	    w14 &= 0x3ffffff;
	    /* k = 15 */
	    lo = Math.imul(al9, bl6);
	    mid = Math.imul(al9, bh6);
	    mid = (mid + Math.imul(ah9, bl6)) | 0;
	    hi = Math.imul(ah9, bh6);
	    lo = (lo + Math.imul(al8, bl7)) | 0;
	    mid = (mid + Math.imul(al8, bh7)) | 0;
	    mid = (mid + Math.imul(ah8, bl7)) | 0;
	    hi = (hi + Math.imul(ah8, bh7)) | 0;
	    lo = (lo + Math.imul(al7, bl8)) | 0;
	    mid = (mid + Math.imul(al7, bh8)) | 0;
	    mid = (mid + Math.imul(ah7, bl8)) | 0;
	    hi = (hi + Math.imul(ah7, bh8)) | 0;
	    lo = (lo + Math.imul(al6, bl9)) | 0;
	    mid = (mid + Math.imul(al6, bh9)) | 0;
	    mid = (mid + Math.imul(ah6, bl9)) | 0;
	    hi = (hi + Math.imul(ah6, bh9)) | 0;
	    var w15 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w15 >>> 26)) | 0;
	    w15 &= 0x3ffffff;
	    /* k = 16 */
	    lo = Math.imul(al9, bl7);
	    mid = Math.imul(al9, bh7);
	    mid = (mid + Math.imul(ah9, bl7)) | 0;
	    hi = Math.imul(ah9, bh7);
	    lo = (lo + Math.imul(al8, bl8)) | 0;
	    mid = (mid + Math.imul(al8, bh8)) | 0;
	    mid = (mid + Math.imul(ah8, bl8)) | 0;
	    hi = (hi + Math.imul(ah8, bh8)) | 0;
	    lo = (lo + Math.imul(al7, bl9)) | 0;
	    mid = (mid + Math.imul(al7, bh9)) | 0;
	    mid = (mid + Math.imul(ah7, bl9)) | 0;
	    hi = (hi + Math.imul(ah7, bh9)) | 0;
	    var w16 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w16 >>> 26)) | 0;
	    w16 &= 0x3ffffff;
	    /* k = 17 */
	    lo = Math.imul(al9, bl8);
	    mid = Math.imul(al9, bh8);
	    mid = (mid + Math.imul(ah9, bl8)) | 0;
	    hi = Math.imul(ah9, bh8);
	    lo = (lo + Math.imul(al8, bl9)) | 0;
	    mid = (mid + Math.imul(al8, bh9)) | 0;
	    mid = (mid + Math.imul(ah8, bl9)) | 0;
	    hi = (hi + Math.imul(ah8, bh9)) | 0;
	    var w17 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w17 >>> 26)) | 0;
	    w17 &= 0x3ffffff;
	    /* k = 18 */
	    lo = Math.imul(al9, bl9);
	    mid = Math.imul(al9, bh9);
	    mid = (mid + Math.imul(ah9, bl9)) | 0;
	    hi = Math.imul(ah9, bh9);
	    var w18 = (((c + lo) | 0) + ((mid & 0x1fff) << 13)) | 0;
	    c = (((hi + (mid >>> 13)) | 0) + (w18 >>> 26)) | 0;
	    w18 &= 0x3ffffff;
	    o[0] = w0;
	    o[1] = w1;
	    o[2] = w2;
	    o[3] = w3;
	    o[4] = w4;
	    o[5] = w5;
	    o[6] = w6;
	    o[7] = w7;
	    o[8] = w8;
	    o[9] = w9;
	    o[10] = w10;
	    o[11] = w11;
	    o[12] = w12;
	    o[13] = w13;
	    o[14] = w14;
	    o[15] = w15;
	    o[16] = w16;
	    o[17] = w17;
	    o[18] = w18;
	    if (c !== 0) {
	      o[19] = c;
	      out.length++;
	    }
	    return out;
	  };

	  // Polyfill comb
	  if (!Math.imul) {
	    comb10MulTo = smallMulTo;
	  }

	  function bigMulTo (self, num, out) {
	    out.negative = num.negative ^ self.negative;
	    out.length = self.length + num.length;

	    var carry = 0;
	    var hncarry = 0;
	    for (var k = 0; k < out.length - 1; k++) {
	      // Sum all words with the same `i + j = k` and accumulate `ncarry`,
	      // note that ncarry could be >= 0x3ffffff
	      var ncarry = hncarry;
	      hncarry = 0;
	      var rword = carry & 0x3ffffff;
	      var maxJ = Math.min(k, num.length - 1);
	      for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
	        var i = k - j;
	        var a = self.words[i] | 0;
	        var b = num.words[j] | 0;
	        var r = a * b;

	        var lo = r & 0x3ffffff;
	        ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
	        lo = (lo + rword) | 0;
	        rword = lo & 0x3ffffff;
	        ncarry = (ncarry + (lo >>> 26)) | 0;

	        hncarry += ncarry >>> 26;
	        ncarry &= 0x3ffffff;
	      }
	      out.words[k] = rword;
	      carry = ncarry;
	      ncarry = hncarry;
	    }
	    if (carry !== 0) {
	      out.words[k] = carry;
	    } else {
	      out.length--;
	    }

	    return out._strip();
	  }

	  function jumboMulTo (self, num, out) {
	    // Temporary disable, see https://github.com/indutny/bn.js/issues/211
	    // var fftm = new FFTM();
	    // return fftm.mulp(self, num, out);
	    return bigMulTo(self, num, out);
	  }

	  BN.prototype.mulTo = function mulTo (num, out) {
	    var res;
	    var len = this.length + num.length;
	    if (this.length === 10 && num.length === 10) {
	      res = comb10MulTo(this, num, out);
	    } else if (len < 63) {
	      res = smallMulTo(this, num, out);
	    } else if (len < 1024) {
	      res = bigMulTo(this, num, out);
	    } else {
	      res = jumboMulTo(this, num, out);
	    }

	    return res;
	  };

	  // Multiply `this` by `num`
	  BN.prototype.mul = function mul (num) {
	    var out = new BN(null);
	    out.words = new Array(this.length + num.length);
	    return this.mulTo(num, out);
	  };

	  // Multiply employing FFT
	  BN.prototype.mulf = function mulf (num) {
	    var out = new BN(null);
	    out.words = new Array(this.length + num.length);
	    return jumboMulTo(this, num, out);
	  };

	  // In-place Multiplication
	  BN.prototype.imul = function imul (num) {
	    return this.clone().mulTo(num, this);
	  };

	  BN.prototype.imuln = function imuln (num) {
	    var isNegNum = num < 0;
	    if (isNegNum) num = -num;

	    assert(typeof num === 'number');
	    assert(num < 0x4000000);

	    // Carry
	    var carry = 0;
	    for (var i = 0; i < this.length; i++) {
	      var w = (this.words[i] | 0) * num;
	      var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
	      carry >>= 26;
	      carry += (w / 0x4000000) | 0;
	      // NOTE: lo is 27bit maximum
	      carry += lo >>> 26;
	      this.words[i] = lo & 0x3ffffff;
	    }

	    if (carry !== 0) {
	      this.words[i] = carry;
	      this.length++;
	    }

	    return isNegNum ? this.ineg() : this;
	  };

	  BN.prototype.muln = function muln (num) {
	    return this.clone().imuln(num);
	  };

	  // `this` * `this`
	  BN.prototype.sqr = function sqr () {
	    return this.mul(this);
	  };

	  // `this` * `this` in-place
	  BN.prototype.isqr = function isqr () {
	    return this.imul(this.clone());
	  };

	  // Math.pow(`this`, `num`)
	  BN.prototype.pow = function pow (num) {
	    var w = toBitArray(num);
	    if (w.length === 0) return new BN(1);

	    // Skip leading zeroes
	    var res = this;
	    for (var i = 0; i < w.length; i++, res = res.sqr()) {
	      if (w[i] !== 0) break;
	    }

	    if (++i < w.length) {
	      for (var q = res.sqr(); i < w.length; i++, q = q.sqr()) {
	        if (w[i] === 0) continue;

	        res = res.mul(q);
	      }
	    }

	    return res;
	  };

	  // Shift-left in-place
	  BN.prototype.iushln = function iushln (bits) {
	    assert(typeof bits === 'number' && bits >= 0);
	    var r = bits % 26;
	    var s = (bits - r) / 26;
	    var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);
	    var i;

	    if (r !== 0) {
	      var carry = 0;

	      for (i = 0; i < this.length; i++) {
	        var newCarry = this.words[i] & carryMask;
	        var c = ((this.words[i] | 0) - newCarry) << r;
	        this.words[i] = c | carry;
	        carry = newCarry >>> (26 - r);
	      }

	      if (carry) {
	        this.words[i] = carry;
	        this.length++;
	      }
	    }

	    if (s !== 0) {
	      for (i = this.length - 1; i >= 0; i--) {
	        this.words[i + s] = this.words[i];
	      }

	      for (i = 0; i < s; i++) {
	        this.words[i] = 0;
	      }

	      this.length += s;
	    }

	    return this._strip();
	  };

	  BN.prototype.ishln = function ishln (bits) {
	    // TODO(indutny): implement me
	    assert(this.negative === 0);
	    return this.iushln(bits);
	  };

	  // Shift-right in-place
	  // NOTE: `hint` is a lowest bit before trailing zeroes
	  // NOTE: if `extended` is present - it will be filled with destroyed bits
	  BN.prototype.iushrn = function iushrn (bits, hint, extended) {
	    assert(typeof bits === 'number' && bits >= 0);
	    var h;
	    if (hint) {
	      h = (hint - (hint % 26)) / 26;
	    } else {
	      h = 0;
	    }

	    var r = bits % 26;
	    var s = Math.min((bits - r) / 26, this.length);
	    var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
	    var maskedWords = extended;

	    h -= s;
	    h = Math.max(0, h);

	    // Extended mode, copy masked part
	    if (maskedWords) {
	      for (var i = 0; i < s; i++) {
	        maskedWords.words[i] = this.words[i];
	      }
	      maskedWords.length = s;
	    }

	    if (s === 0) ; else if (this.length > s) {
	      this.length -= s;
	      for (i = 0; i < this.length; i++) {
	        this.words[i] = this.words[i + s];
	      }
	    } else {
	      this.words[0] = 0;
	      this.length = 1;
	    }

	    var carry = 0;
	    for (i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
	      var word = this.words[i] | 0;
	      this.words[i] = (carry << (26 - r)) | (word >>> r);
	      carry = word & mask;
	    }

	    // Push carried bits as a mask
	    if (maskedWords && carry !== 0) {
	      maskedWords.words[maskedWords.length++] = carry;
	    }

	    if (this.length === 0) {
	      this.words[0] = 0;
	      this.length = 1;
	    }

	    return this._strip();
	  };

	  BN.prototype.ishrn = function ishrn (bits, hint, extended) {
	    // TODO(indutny): implement me
	    assert(this.negative === 0);
	    return this.iushrn(bits, hint, extended);
	  };

	  // Shift-left
	  BN.prototype.shln = function shln (bits) {
	    return this.clone().ishln(bits);
	  };

	  BN.prototype.ushln = function ushln (bits) {
	    return this.clone().iushln(bits);
	  };

	  // Shift-right
	  BN.prototype.shrn = function shrn (bits) {
	    return this.clone().ishrn(bits);
	  };

	  BN.prototype.ushrn = function ushrn (bits) {
	    return this.clone().iushrn(bits);
	  };

	  // Test if n bit is set
	  BN.prototype.testn = function testn (bit) {
	    assert(typeof bit === 'number' && bit >= 0);
	    var r = bit % 26;
	    var s = (bit - r) / 26;
	    var q = 1 << r;

	    // Fast case: bit is much higher than all existing words
	    if (this.length <= s) return false;

	    // Check bit and return
	    var w = this.words[s];

	    return !!(w & q);
	  };

	  // Return only lowers bits of number (in-place)
	  BN.prototype.imaskn = function imaskn (bits) {
	    assert(typeof bits === 'number' && bits >= 0);
	    var r = bits % 26;
	    var s = (bits - r) / 26;

	    assert(this.negative === 0, 'imaskn works only with positive numbers');

	    if (this.length <= s) {
	      return this;
	    }

	    if (r !== 0) {
	      s++;
	    }
	    this.length = Math.min(s, this.length);

	    if (r !== 0) {
	      var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
	      this.words[this.length - 1] &= mask;
	    }

	    return this._strip();
	  };

	  // Return only lowers bits of number
	  BN.prototype.maskn = function maskn (bits) {
	    return this.clone().imaskn(bits);
	  };

	  // Add plain number `num` to `this`
	  BN.prototype.iaddn = function iaddn (num) {
	    assert(typeof num === 'number');
	    assert(num < 0x4000000);
	    if (num < 0) return this.isubn(-num);

	    // Possible sign change
	    if (this.negative !== 0) {
	      if (this.length === 1 && (this.words[0] | 0) <= num) {
	        this.words[0] = num - (this.words[0] | 0);
	        this.negative = 0;
	        return this;
	      }

	      this.negative = 0;
	      this.isubn(num);
	      this.negative = 1;
	      return this;
	    }

	    // Add without checks
	    return this._iaddn(num);
	  };

	  BN.prototype._iaddn = function _iaddn (num) {
	    this.words[0] += num;

	    // Carry
	    for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
	      this.words[i] -= 0x4000000;
	      if (i === this.length - 1) {
	        this.words[i + 1] = 1;
	      } else {
	        this.words[i + 1]++;
	      }
	    }
	    this.length = Math.max(this.length, i + 1);

	    return this;
	  };

	  // Subtract plain number `num` from `this`
	  BN.prototype.isubn = function isubn (num) {
	    assert(typeof num === 'number');
	    assert(num < 0x4000000);
	    if (num < 0) return this.iaddn(-num);

	    if (this.negative !== 0) {
	      this.negative = 0;
	      this.iaddn(num);
	      this.negative = 1;
	      return this;
	    }

	    this.words[0] -= num;

	    if (this.length === 1 && this.words[0] < 0) {
	      this.words[0] = -this.words[0];
	      this.negative = 1;
	    } else {
	      // Carry
	      for (var i = 0; i < this.length && this.words[i] < 0; i++) {
	        this.words[i] += 0x4000000;
	        this.words[i + 1] -= 1;
	      }
	    }

	    return this._strip();
	  };

	  BN.prototype.addn = function addn (num) {
	    return this.clone().iaddn(num);
	  };

	  BN.prototype.subn = function subn (num) {
	    return this.clone().isubn(num);
	  };

	  BN.prototype.iabs = function iabs () {
	    this.negative = 0;

	    return this;
	  };

	  BN.prototype.abs = function abs () {
	    return this.clone().iabs();
	  };

	  BN.prototype._ishlnsubmul = function _ishlnsubmul (num, mul, shift) {
	    var len = num.length + shift;
	    var i;

	    this._expand(len);

	    var w;
	    var carry = 0;
	    for (i = 0; i < num.length; i++) {
	      w = (this.words[i + shift] | 0) + carry;
	      var right = (num.words[i] | 0) * mul;
	      w -= right & 0x3ffffff;
	      carry = (w >> 26) - ((right / 0x4000000) | 0);
	      this.words[i + shift] = w & 0x3ffffff;
	    }
	    for (; i < this.length - shift; i++) {
	      w = (this.words[i + shift] | 0) + carry;
	      carry = w >> 26;
	      this.words[i + shift] = w & 0x3ffffff;
	    }

	    if (carry === 0) return this._strip();

	    // Subtraction overflow
	    assert(carry === -1);
	    carry = 0;
	    for (i = 0; i < this.length; i++) {
	      w = -(this.words[i] | 0) + carry;
	      carry = w >> 26;
	      this.words[i] = w & 0x3ffffff;
	    }
	    this.negative = 1;

	    return this._strip();
	  };

	  BN.prototype._wordDiv = function _wordDiv (num, mode) {
	    var shift = this.length - num.length;

	    var a = this.clone();
	    var b = num;

	    // Normalize
	    var bhi = b.words[b.length - 1] | 0;
	    var bhiBits = this._countBits(bhi);
	    shift = 26 - bhiBits;
	    if (shift !== 0) {
	      b = b.ushln(shift);
	      a.iushln(shift);
	      bhi = b.words[b.length - 1] | 0;
	    }

	    // Initialize quotient
	    var m = a.length - b.length;
	    var q;

	    if (mode !== 'mod') {
	      q = new BN(null);
	      q.length = m + 1;
	      q.words = new Array(q.length);
	      for (var i = 0; i < q.length; i++) {
	        q.words[i] = 0;
	      }
	    }

	    var diff = a.clone()._ishlnsubmul(b, 1, m);
	    if (diff.negative === 0) {
	      a = diff;
	      if (q) {
	        q.words[m] = 1;
	      }
	    }

	    for (var j = m - 1; j >= 0; j--) {
	      var qj = (a.words[b.length + j] | 0) * 0x4000000 +
	        (a.words[b.length + j - 1] | 0);

	      // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
	      // (0x7ffffff)
	      qj = Math.min((qj / bhi) | 0, 0x3ffffff);

	      a._ishlnsubmul(b, qj, j);
	      while (a.negative !== 0) {
	        qj--;
	        a.negative = 0;
	        a._ishlnsubmul(b, 1, j);
	        if (!a.isZero()) {
	          a.negative ^= 1;
	        }
	      }
	      if (q) {
	        q.words[j] = qj;
	      }
	    }
	    if (q) {
	      q._strip();
	    }
	    a._strip();

	    // Denormalize
	    if (mode !== 'div' && shift !== 0) {
	      a.iushrn(shift);
	    }

	    return {
	      div: q || null,
	      mod: a
	    };
	  };

	  // NOTE: 1) `mode` can be set to `mod` to request mod only,
	  //       to `div` to request div only, or be absent to
	  //       request both div & mod
	  //       2) `positive` is true if unsigned mod is requested
	  BN.prototype.divmod = function divmod (num, mode, positive) {
	    assert(!num.isZero());

	    if (this.isZero()) {
	      return {
	        div: new BN(0),
	        mod: new BN(0)
	      };
	    }

	    var div, mod, res;
	    if (this.negative !== 0 && num.negative === 0) {
	      res = this.neg().divmod(num, mode);

	      if (mode !== 'mod') {
	        div = res.div.neg();
	      }

	      if (mode !== 'div') {
	        mod = res.mod.neg();
	        if (positive && mod.negative !== 0) {
	          mod.iadd(num);
	        }
	      }

	      return {
	        div: div,
	        mod: mod
	      };
	    }

	    if (this.negative === 0 && num.negative !== 0) {
	      res = this.divmod(num.neg(), mode);

	      if (mode !== 'mod') {
	        div = res.div.neg();
	      }

	      return {
	        div: div,
	        mod: res.mod
	      };
	    }

	    if ((this.negative & num.negative) !== 0) {
	      res = this.neg().divmod(num.neg(), mode);

	      if (mode !== 'div') {
	        mod = res.mod.neg();
	        if (positive && mod.negative !== 0) {
	          mod.isub(num);
	        }
	      }

	      return {
	        div: res.div,
	        mod: mod
	      };
	    }

	    // Both numbers are positive at this point

	    // Strip both numbers to approximate shift value
	    if (num.length > this.length || this.cmp(num) < 0) {
	      return {
	        div: new BN(0),
	        mod: this
	      };
	    }

	    // Very short reduction
	    if (num.length === 1) {
	      if (mode === 'div') {
	        return {
	          div: this.divn(num.words[0]),
	          mod: null
	        };
	      }

	      if (mode === 'mod') {
	        return {
	          div: null,
	          mod: new BN(this.modrn(num.words[0]))
	        };
	      }

	      return {
	        div: this.divn(num.words[0]),
	        mod: new BN(this.modrn(num.words[0]))
	      };
	    }

	    return this._wordDiv(num, mode);
	  };

	  // Find `this` / `num`
	  BN.prototype.div = function div (num) {
	    return this.divmod(num, 'div', false).div;
	  };

	  // Find `this` % `num`
	  BN.prototype.mod = function mod (num) {
	    return this.divmod(num, 'mod', false).mod;
	  };

	  BN.prototype.umod = function umod (num) {
	    return this.divmod(num, 'mod', true).mod;
	  };

	  // Find Round(`this` / `num`)
	  BN.prototype.divRound = function divRound (num) {
	    var dm = this.divmod(num);

	    // Fast case - exact division
	    if (dm.mod.isZero()) return dm.div;

	    var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

	    var half = num.ushrn(1);
	    var r2 = num.andln(1);
	    var cmp = mod.cmp(half);

	    // Round down
	    if (cmp < 0 || (r2 === 1 && cmp === 0)) return dm.div;

	    // Round up
	    return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
	  };

	  BN.prototype.modrn = function modrn (num) {
	    var isNegNum = num < 0;
	    if (isNegNum) num = -num;

	    assert(num <= 0x3ffffff);
	    var p = (1 << 26) % num;

	    var acc = 0;
	    for (var i = this.length - 1; i >= 0; i--) {
	      acc = (p * acc + (this.words[i] | 0)) % num;
	    }

	    return isNegNum ? -acc : acc;
	  };

	  // WARNING: DEPRECATED
	  BN.prototype.modn = function modn (num) {
	    return this.modrn(num);
	  };

	  // In-place division by number
	  BN.prototype.idivn = function idivn (num) {
	    var isNegNum = num < 0;
	    if (isNegNum) num = -num;

	    assert(num <= 0x3ffffff);

	    var carry = 0;
	    for (var i = this.length - 1; i >= 0; i--) {
	      var w = (this.words[i] | 0) + carry * 0x4000000;
	      this.words[i] = (w / num) | 0;
	      carry = w % num;
	    }

	    this._strip();
	    return isNegNum ? this.ineg() : this;
	  };

	  BN.prototype.divn = function divn (num) {
	    return this.clone().idivn(num);
	  };

	  BN.prototype.egcd = function egcd (p) {
	    assert(p.negative === 0);
	    assert(!p.isZero());

	    var x = this;
	    var y = p.clone();

	    if (x.negative !== 0) {
	      x = x.umod(p);
	    } else {
	      x = x.clone();
	    }

	    // A * x + B * y = x
	    var A = new BN(1);
	    var B = new BN(0);

	    // C * x + D * y = y
	    var C = new BN(0);
	    var D = new BN(1);

	    var g = 0;

	    while (x.isEven() && y.isEven()) {
	      x.iushrn(1);
	      y.iushrn(1);
	      ++g;
	    }

	    var yp = y.clone();
	    var xp = x.clone();

	    while (!x.isZero()) {
	      for (var i = 0, im = 1; (x.words[0] & im) === 0 && i < 26; ++i, im <<= 1);
	      if (i > 0) {
	        x.iushrn(i);
	        while (i-- > 0) {
	          if (A.isOdd() || B.isOdd()) {
	            A.iadd(yp);
	            B.isub(xp);
	          }

	          A.iushrn(1);
	          B.iushrn(1);
	        }
	      }

	      for (var j = 0, jm = 1; (y.words[0] & jm) === 0 && j < 26; ++j, jm <<= 1);
	      if (j > 0) {
	        y.iushrn(j);
	        while (j-- > 0) {
	          if (C.isOdd() || D.isOdd()) {
	            C.iadd(yp);
	            D.isub(xp);
	          }

	          C.iushrn(1);
	          D.iushrn(1);
	        }
	      }

	      if (x.cmp(y) >= 0) {
	        x.isub(y);
	        A.isub(C);
	        B.isub(D);
	      } else {
	        y.isub(x);
	        C.isub(A);
	        D.isub(B);
	      }
	    }

	    return {
	      a: C,
	      b: D,
	      gcd: y.iushln(g)
	    };
	  };

	  // This is reduced incarnation of the binary EEA
	  // above, designated to invert members of the
	  // _prime_ fields F(p) at a maximal speed
	  BN.prototype._invmp = function _invmp (p) {
	    assert(p.negative === 0);
	    assert(!p.isZero());

	    var a = this;
	    var b = p.clone();

	    if (a.negative !== 0) {
	      a = a.umod(p);
	    } else {
	      a = a.clone();
	    }

	    var x1 = new BN(1);
	    var x2 = new BN(0);

	    var delta = b.clone();

	    while (a.cmpn(1) > 0 && b.cmpn(1) > 0) {
	      for (var i = 0, im = 1; (a.words[0] & im) === 0 && i < 26; ++i, im <<= 1);
	      if (i > 0) {
	        a.iushrn(i);
	        while (i-- > 0) {
	          if (x1.isOdd()) {
	            x1.iadd(delta);
	          }

	          x1.iushrn(1);
	        }
	      }

	      for (var j = 0, jm = 1; (b.words[0] & jm) === 0 && j < 26; ++j, jm <<= 1);
	      if (j > 0) {
	        b.iushrn(j);
	        while (j-- > 0) {
	          if (x2.isOdd()) {
	            x2.iadd(delta);
	          }

	          x2.iushrn(1);
	        }
	      }

	      if (a.cmp(b) >= 0) {
	        a.isub(b);
	        x1.isub(x2);
	      } else {
	        b.isub(a);
	        x2.isub(x1);
	      }
	    }

	    var res;
	    if (a.cmpn(1) === 0) {
	      res = x1;
	    } else {
	      res = x2;
	    }

	    if (res.cmpn(0) < 0) {
	      res.iadd(p);
	    }

	    return res;
	  };

	  BN.prototype.gcd = function gcd (num) {
	    if (this.isZero()) return num.abs();
	    if (num.isZero()) return this.abs();

	    var a = this.clone();
	    var b = num.clone();
	    a.negative = 0;
	    b.negative = 0;

	    // Remove common factor of two
	    for (var shift = 0; a.isEven() && b.isEven(); shift++) {
	      a.iushrn(1);
	      b.iushrn(1);
	    }

	    do {
	      while (a.isEven()) {
	        a.iushrn(1);
	      }
	      while (b.isEven()) {
	        b.iushrn(1);
	      }

	      var r = a.cmp(b);
	      if (r < 0) {
	        // Swap `a` and `b` to make `a` always bigger than `b`
	        var t = a;
	        a = b;
	        b = t;
	      } else if (r === 0 || b.cmpn(1) === 0) {
	        break;
	      }

	      a.isub(b);
	    } while (true);

	    return b.iushln(shift);
	  };

	  // Invert number in the field F(num)
	  BN.prototype.invm = function invm (num) {
	    return this.egcd(num).a.umod(num);
	  };

	  BN.prototype.isEven = function isEven () {
	    return (this.words[0] & 1) === 0;
	  };

	  BN.prototype.isOdd = function isOdd () {
	    return (this.words[0] & 1) === 1;
	  };

	  // And first word and num
	  BN.prototype.andln = function andln (num) {
	    return this.words[0] & num;
	  };

	  // Increment at the bit position in-line
	  BN.prototype.bincn = function bincn (bit) {
	    assert(typeof bit === 'number');
	    var r = bit % 26;
	    var s = (bit - r) / 26;
	    var q = 1 << r;

	    // Fast case: bit is much higher than all existing words
	    if (this.length <= s) {
	      this._expand(s + 1);
	      this.words[s] |= q;
	      return this;
	    }

	    // Add bit and propagate, if needed
	    var carry = q;
	    for (var i = s; carry !== 0 && i < this.length; i++) {
	      var w = this.words[i] | 0;
	      w += carry;
	      carry = w >>> 26;
	      w &= 0x3ffffff;
	      this.words[i] = w;
	    }
	    if (carry !== 0) {
	      this.words[i] = carry;
	      this.length++;
	    }
	    return this;
	  };

	  BN.prototype.isZero = function isZero () {
	    return this.length === 1 && this.words[0] === 0;
	  };

	  BN.prototype.cmpn = function cmpn (num) {
	    var negative = num < 0;

	    if (this.negative !== 0 && !negative) return -1;
	    if (this.negative === 0 && negative) return 1;

	    this._strip();

	    var res;
	    if (this.length > 1) {
	      res = 1;
	    } else {
	      if (negative) {
	        num = -num;
	      }

	      assert(num <= 0x3ffffff, 'Number is too big');

	      var w = this.words[0] | 0;
	      res = w === num ? 0 : w < num ? -1 : 1;
	    }
	    if (this.negative !== 0) return -res | 0;
	    return res;
	  };

	  // Compare two numbers and return:
	  // 1 - if `this` > `num`
	  // 0 - if `this` == `num`
	  // -1 - if `this` < `num`
	  BN.prototype.cmp = function cmp (num) {
	    if (this.negative !== 0 && num.negative === 0) return -1;
	    if (this.negative === 0 && num.negative !== 0) return 1;

	    var res = this.ucmp(num);
	    if (this.negative !== 0) return -res | 0;
	    return res;
	  };

	  // Unsigned comparison
	  BN.prototype.ucmp = function ucmp (num) {
	    // At this point both numbers have the same sign
	    if (this.length > num.length) return 1;
	    if (this.length < num.length) return -1;

	    var res = 0;
	    for (var i = this.length - 1; i >= 0; i--) {
	      var a = this.words[i] | 0;
	      var b = num.words[i] | 0;

	      if (a === b) continue;
	      if (a < b) {
	        res = -1;
	      } else if (a > b) {
	        res = 1;
	      }
	      break;
	    }
	    return res;
	  };

	  BN.prototype.gtn = function gtn (num) {
	    return this.cmpn(num) === 1;
	  };

	  BN.prototype.gt = function gt (num) {
	    return this.cmp(num) === 1;
	  };

	  BN.prototype.gten = function gten (num) {
	    return this.cmpn(num) >= 0;
	  };

	  BN.prototype.gte = function gte (num) {
	    return this.cmp(num) >= 0;
	  };

	  BN.prototype.ltn = function ltn (num) {
	    return this.cmpn(num) === -1;
	  };

	  BN.prototype.lt = function lt (num) {
	    return this.cmp(num) === -1;
	  };

	  BN.prototype.lten = function lten (num) {
	    return this.cmpn(num) <= 0;
	  };

	  BN.prototype.lte = function lte (num) {
	    return this.cmp(num) <= 0;
	  };

	  BN.prototype.eqn = function eqn (num) {
	    return this.cmpn(num) === 0;
	  };

	  BN.prototype.eq = function eq (num) {
	    return this.cmp(num) === 0;
	  };

	  //
	  // A reduce context, could be using montgomery or something better, depending
	  // on the `m` itself.
	  //
	  BN.red = function red (num) {
	    return new Red(num);
	  };

	  BN.prototype.toRed = function toRed (ctx) {
	    assert(!this.red, 'Already a number in reduction context');
	    assert(this.negative === 0, 'red works only with positives');
	    return ctx.convertTo(this)._forceRed(ctx);
	  };

	  BN.prototype.fromRed = function fromRed () {
	    assert(this.red, 'fromRed works only with numbers in reduction context');
	    return this.red.convertFrom(this);
	  };

	  BN.prototype._forceRed = function _forceRed (ctx) {
	    this.red = ctx;
	    return this;
	  };

	  BN.prototype.forceRed = function forceRed (ctx) {
	    assert(!this.red, 'Already a number in reduction context');
	    return this._forceRed(ctx);
	  };

	  BN.prototype.redAdd = function redAdd (num) {
	    assert(this.red, 'redAdd works only with red numbers');
	    return this.red.add(this, num);
	  };

	  BN.prototype.redIAdd = function redIAdd (num) {
	    assert(this.red, 'redIAdd works only with red numbers');
	    return this.red.iadd(this, num);
	  };

	  BN.prototype.redSub = function redSub (num) {
	    assert(this.red, 'redSub works only with red numbers');
	    return this.red.sub(this, num);
	  };

	  BN.prototype.redISub = function redISub (num) {
	    assert(this.red, 'redISub works only with red numbers');
	    return this.red.isub(this, num);
	  };

	  BN.prototype.redShl = function redShl (num) {
	    assert(this.red, 'redShl works only with red numbers');
	    return this.red.shl(this, num);
	  };

	  BN.prototype.redMul = function redMul (num) {
	    assert(this.red, 'redMul works only with red numbers');
	    this.red._verify2(this, num);
	    return this.red.mul(this, num);
	  };

	  BN.prototype.redIMul = function redIMul (num) {
	    assert(this.red, 'redMul works only with red numbers');
	    this.red._verify2(this, num);
	    return this.red.imul(this, num);
	  };

	  BN.prototype.redSqr = function redSqr () {
	    assert(this.red, 'redSqr works only with red numbers');
	    this.red._verify1(this);
	    return this.red.sqr(this);
	  };

	  BN.prototype.redISqr = function redISqr () {
	    assert(this.red, 'redISqr works only with red numbers');
	    this.red._verify1(this);
	    return this.red.isqr(this);
	  };

	  // Square root over p
	  BN.prototype.redSqrt = function redSqrt () {
	    assert(this.red, 'redSqrt works only with red numbers');
	    this.red._verify1(this);
	    return this.red.sqrt(this);
	  };

	  BN.prototype.redInvm = function redInvm () {
	    assert(this.red, 'redInvm works only with red numbers');
	    this.red._verify1(this);
	    return this.red.invm(this);
	  };

	  // Return negative clone of `this` % `red modulo`
	  BN.prototype.redNeg = function redNeg () {
	    assert(this.red, 'redNeg works only with red numbers');
	    this.red._verify1(this);
	    return this.red.neg(this);
	  };

	  BN.prototype.redPow = function redPow (num) {
	    assert(this.red && !num.red, 'redPow(normalNum)');
	    this.red._verify1(this);
	    return this.red.pow(this, num);
	  };

	  // Prime numbers with efficient reduction
	  var primes = {
	    k256: null,
	    p224: null,
	    p192: null,
	    p25519: null
	  };

	  // Pseudo-Mersenne prime
	  function MPrime (name, p) {
	    // P = 2 ^ N - K
	    this.name = name;
	    this.p = new BN(p, 16);
	    this.n = this.p.bitLength();
	    this.k = new BN(1).iushln(this.n).isub(this.p);

	    this.tmp = this._tmp();
	  }

	  MPrime.prototype._tmp = function _tmp () {
	    var tmp = new BN(null);
	    tmp.words = new Array(Math.ceil(this.n / 13));
	    return tmp;
	  };

	  MPrime.prototype.ireduce = function ireduce (num) {
	    // Assumes that `num` is less than `P^2`
	    // num = HI * (2 ^ N - K) + HI * K + LO = HI * K + LO (mod P)
	    var r = num;
	    var rlen;

	    do {
	      this.split(r, this.tmp);
	      r = this.imulK(r);
	      r = r.iadd(this.tmp);
	      rlen = r.bitLength();
	    } while (rlen > this.n);

	    var cmp = rlen < this.n ? -1 : r.ucmp(this.p);
	    if (cmp === 0) {
	      r.words[0] = 0;
	      r.length = 1;
	    } else if (cmp > 0) {
	      r.isub(this.p);
	    } else {
	      if (r.strip !== undefined) {
	        // r is a BN v4 instance
	        r.strip();
	      } else {
	        // r is a BN v5 instance
	        r._strip();
	      }
	    }

	    return r;
	  };

	  MPrime.prototype.split = function split (input, out) {
	    input.iushrn(this.n, 0, out);
	  };

	  MPrime.prototype.imulK = function imulK (num) {
	    return num.imul(this.k);
	  };

	  function K256 () {
	    MPrime.call(
	      this,
	      'k256',
	      'ffffffff ffffffff ffffffff ffffffff ffffffff ffffffff fffffffe fffffc2f');
	  }
	  inherits(K256, MPrime);

	  K256.prototype.split = function split (input, output) {
	    // 256 = 9 * 26 + 22
	    var mask = 0x3fffff;

	    var outLen = Math.min(input.length, 9);
	    for (var i = 0; i < outLen; i++) {
	      output.words[i] = input.words[i];
	    }
	    output.length = outLen;

	    if (input.length <= 9) {
	      input.words[0] = 0;
	      input.length = 1;
	      return;
	    }

	    // Shift by 9 limbs
	    var prev = input.words[9];
	    output.words[output.length++] = prev & mask;

	    for (i = 10; i < input.length; i++) {
	      var next = input.words[i] | 0;
	      input.words[i - 10] = ((next & mask) << 4) | (prev >>> 22);
	      prev = next;
	    }
	    prev >>>= 22;
	    input.words[i - 10] = prev;
	    if (prev === 0 && input.length > 10) {
	      input.length -= 10;
	    } else {
	      input.length -= 9;
	    }
	  };

	  K256.prototype.imulK = function imulK (num) {
	    // K = 0x1000003d1 = [ 0x40, 0x3d1 ]
	    num.words[num.length] = 0;
	    num.words[num.length + 1] = 0;
	    num.length += 2;

	    // bounded at: 0x40 * 0x3ffffff + 0x3d0 = 0x100000390
	    var lo = 0;
	    for (var i = 0; i < num.length; i++) {
	      var w = num.words[i] | 0;
	      lo += w * 0x3d1;
	      num.words[i] = lo & 0x3ffffff;
	      lo = w * 0x40 + ((lo / 0x4000000) | 0);
	    }

	    // Fast length reduction
	    if (num.words[num.length - 1] === 0) {
	      num.length--;
	      if (num.words[num.length - 1] === 0) {
	        num.length--;
	      }
	    }
	    return num;
	  };

	  function P224 () {
	    MPrime.call(
	      this,
	      'p224',
	      'ffffffff ffffffff ffffffff ffffffff 00000000 00000000 00000001');
	  }
	  inherits(P224, MPrime);

	  function P192 () {
	    MPrime.call(
	      this,
	      'p192',
	      'ffffffff ffffffff ffffffff fffffffe ffffffff ffffffff');
	  }
	  inherits(P192, MPrime);

	  function P25519 () {
	    // 2 ^ 255 - 19
	    MPrime.call(
	      this,
	      '25519',
	      '7fffffffffffffff ffffffffffffffff ffffffffffffffff ffffffffffffffed');
	  }
	  inherits(P25519, MPrime);

	  P25519.prototype.imulK = function imulK (num) {
	    // K = 0x13
	    var carry = 0;
	    for (var i = 0; i < num.length; i++) {
	      var hi = (num.words[i] | 0) * 0x13 + carry;
	      var lo = hi & 0x3ffffff;
	      hi >>>= 26;

	      num.words[i] = lo;
	      carry = hi;
	    }
	    if (carry !== 0) {
	      num.words[num.length++] = carry;
	    }
	    return num;
	  };

	  // Exported mostly for testing purposes, use plain name instead
	  BN._prime = function prime (name) {
	    // Cached version of prime
	    if (primes[name]) return primes[name];

	    var prime;
	    if (name === 'k256') {
	      prime = new K256();
	    } else if (name === 'p224') {
	      prime = new P224();
	    } else if (name === 'p192') {
	      prime = new P192();
	    } else if (name === 'p25519') {
	      prime = new P25519();
	    } else {
	      throw new Error('Unknown prime ' + name);
	    }
	    primes[name] = prime;

	    return prime;
	  };

	  //
	  // Base reduction engine
	  //
	  function Red (m) {
	    if (typeof m === 'string') {
	      var prime = BN._prime(m);
	      this.m = prime.p;
	      this.prime = prime;
	    } else {
	      assert(m.gtn(1), 'modulus must be greater than 1');
	      this.m = m;
	      this.prime = null;
	    }
	  }

	  Red.prototype._verify1 = function _verify1 (a) {
	    assert(a.negative === 0, 'red works only with positives');
	    assert(a.red, 'red works only with red numbers');
	  };

	  Red.prototype._verify2 = function _verify2 (a, b) {
	    assert((a.negative | b.negative) === 0, 'red works only with positives');
	    assert(a.red && a.red === b.red,
	      'red works only with red numbers');
	  };

	  Red.prototype.imod = function imod (a) {
	    if (this.prime) return this.prime.ireduce(a)._forceRed(this);

	    move(a, a.umod(this.m)._forceRed(this));
	    return a;
	  };

	  Red.prototype.neg = function neg (a) {
	    if (a.isZero()) {
	      return a.clone();
	    }

	    return this.m.sub(a)._forceRed(this);
	  };

	  Red.prototype.add = function add (a, b) {
	    this._verify2(a, b);

	    var res = a.add(b);
	    if (res.cmp(this.m) >= 0) {
	      res.isub(this.m);
	    }
	    return res._forceRed(this);
	  };

	  Red.prototype.iadd = function iadd (a, b) {
	    this._verify2(a, b);

	    var res = a.iadd(b);
	    if (res.cmp(this.m) >= 0) {
	      res.isub(this.m);
	    }
	    return res;
	  };

	  Red.prototype.sub = function sub (a, b) {
	    this._verify2(a, b);

	    var res = a.sub(b);
	    if (res.cmpn(0) < 0) {
	      res.iadd(this.m);
	    }
	    return res._forceRed(this);
	  };

	  Red.prototype.isub = function isub (a, b) {
	    this._verify2(a, b);

	    var res = a.isub(b);
	    if (res.cmpn(0) < 0) {
	      res.iadd(this.m);
	    }
	    return res;
	  };

	  Red.prototype.shl = function shl (a, num) {
	    this._verify1(a);
	    return this.imod(a.ushln(num));
	  };

	  Red.prototype.imul = function imul (a, b) {
	    this._verify2(a, b);
	    return this.imod(a.imul(b));
	  };

	  Red.prototype.mul = function mul (a, b) {
	    this._verify2(a, b);
	    return this.imod(a.mul(b));
	  };

	  Red.prototype.isqr = function isqr (a) {
	    return this.imul(a, a.clone());
	  };

	  Red.prototype.sqr = function sqr (a) {
	    return this.mul(a, a);
	  };

	  Red.prototype.sqrt = function sqrt (a) {
	    if (a.isZero()) return a.clone();

	    var mod3 = this.m.andln(3);
	    assert(mod3 % 2 === 1);

	    // Fast case
	    if (mod3 === 3) {
	      var pow = this.m.add(new BN(1)).iushrn(2);
	      return this.pow(a, pow);
	    }

	    // Tonelli-Shanks algorithm (Totally unoptimized and slow)
	    //
	    // Find Q and S, that Q * 2 ^ S = (P - 1)
	    var q = this.m.subn(1);
	    var s = 0;
	    while (!q.isZero() && q.andln(1) === 0) {
	      s++;
	      q.iushrn(1);
	    }
	    assert(!q.isZero());

	    var one = new BN(1).toRed(this);
	    var nOne = one.redNeg();

	    // Find quadratic non-residue
	    // NOTE: Max is such because of generalized Riemann hypothesis.
	    var lpow = this.m.subn(1).iushrn(1);
	    var z = this.m.bitLength();
	    z = new BN(2 * z * z).toRed(this);

	    while (this.pow(z, lpow).cmp(nOne) !== 0) {
	      z.redIAdd(nOne);
	    }

	    var c = this.pow(z, q);
	    var r = this.pow(a, q.addn(1).iushrn(1));
	    var t = this.pow(a, q);
	    var m = s;
	    while (t.cmp(one) !== 0) {
	      var tmp = t;
	      for (var i = 0; tmp.cmp(one) !== 0; i++) {
	        tmp = tmp.redSqr();
	      }
	      assert(i < m);
	      var b = this.pow(c, new BN(1).iushln(m - i - 1));

	      r = r.redMul(b);
	      c = b.redSqr();
	      t = t.redMul(c);
	      m = i;
	    }

	    return r;
	  };

	  Red.prototype.invm = function invm (a) {
	    var inv = a._invmp(this.m);
	    if (inv.negative !== 0) {
	      inv.negative = 0;
	      return this.imod(inv).redNeg();
	    } else {
	      return this.imod(inv);
	    }
	  };

	  Red.prototype.pow = function pow (a, num) {
	    if (num.isZero()) return new BN(1).toRed(this);
	    if (num.cmpn(1) === 0) return a.clone();

	    var windowSize = 4;
	    var wnd = new Array(1 << windowSize);
	    wnd[0] = new BN(1).toRed(this);
	    wnd[1] = a;
	    for (var i = 2; i < wnd.length; i++) {
	      wnd[i] = this.mul(wnd[i - 1], a);
	    }

	    var res = wnd[0];
	    var current = 0;
	    var currentLen = 0;
	    var start = num.bitLength() % 26;
	    if (start === 0) {
	      start = 26;
	    }

	    for (i = num.length - 1; i >= 0; i--) {
	      var word = num.words[i];
	      for (var j = start - 1; j >= 0; j--) {
	        var bit = (word >> j) & 1;
	        if (res !== wnd[0]) {
	          res = this.sqr(res);
	        }

	        if (bit === 0 && current === 0) {
	          currentLen = 0;
	          continue;
	        }

	        current <<= 1;
	        current |= bit;
	        currentLen++;
	        if (currentLen !== windowSize && (i !== 0 || j !== 0)) continue;

	        res = this.mul(res, wnd[current]);
	        currentLen = 0;
	        current = 0;
	      }
	      start = 26;
	    }

	    return res;
	  };

	  Red.prototype.convertTo = function convertTo (num) {
	    var r = num.umod(this.m);

	    return r === num ? r.clone() : r;
	  };

	  Red.prototype.convertFrom = function convertFrom (num) {
	    var res = num.clone();
	    res.red = null;
	    return res;
	  };

	  //
	  // Montgomery method engine
	  //

	  BN.mont = function mont (num) {
	    return new Mont(num);
	  };

	  function Mont (m) {
	    Red.call(this, m);

	    this.shift = this.m.bitLength();
	    if (this.shift % 26 !== 0) {
	      this.shift += 26 - (this.shift % 26);
	    }

	    this.r = new BN(1).iushln(this.shift);
	    this.r2 = this.imod(this.r.sqr());
	    this.rinv = this.r._invmp(this.m);

	    this.minv = this.rinv.mul(this.r).isubn(1).div(this.m);
	    this.minv = this.minv.umod(this.r);
	    this.minv = this.r.sub(this.minv);
	  }
	  inherits(Mont, Red);

	  Mont.prototype.convertTo = function convertTo (num) {
	    return this.imod(num.ushln(this.shift));
	  };

	  Mont.prototype.convertFrom = function convertFrom (num) {
	    var r = this.imod(num.mul(this.rinv));
	    r.red = null;
	    return r;
	  };

	  Mont.prototype.imul = function imul (a, b) {
	    if (a.isZero() || b.isZero()) {
	      a.words[0] = 0;
	      a.length = 1;
	      return a;
	    }

	    var t = a.imul(b);
	    var c = t.maskn(this.shift).mul(this.minv).imaskn(this.shift).mul(this.m);
	    var u = t.isub(c).iushrn(this.shift);
	    var res = u;

	    if (u.cmp(this.m) >= 0) {
	      res = u.isub(this.m);
	    } else if (u.cmpn(0) < 0) {
	      res = u.iadd(this.m);
	    }

	    return res._forceRed(this);
	  };

	  Mont.prototype.mul = function mul (a, b) {
	    if (a.isZero() || b.isZero()) return new BN(0)._forceRed(this);

	    var t = a.mul(b);
	    var c = t.maskn(this.shift).mul(this.minv).imaskn(this.shift).mul(this.m);
	    var u = t.isub(c).iushrn(this.shift);
	    var res = u;
	    if (u.cmp(this.m) >= 0) {
	      res = u.isub(this.m);
	    } else if (u.cmpn(0) < 0) {
	      res = u.iadd(this.m);
	    }

	    return res._forceRed(this);
	  };

	  Mont.prototype.invm = function invm (a) {
	    // (AR)^-1 * R^2 = (A^-1 * R^-1) * R^2 = A^-1 * R
	    var res = this.imod(a._invmp(this.m).mul(this.r2));
	    return res._forceRed(this);
	  };
	})(module, commonjsGlobal); 
} (bn));

var bnExports = bn.exports;
var _BN = /*@__PURE__*/getDefaultExportFromCjs(bnExports);

const version$3 = "logger/5.7.0";

let _permanentCensorErrors = false;
let _censorErrors = false;
const LogLevels = { debug: 1, "default": 2, info: 2, warning: 3, error: 4, off: 5 };
let _logLevel = LogLevels["default"];
let _globalLogger = null;
function _checkNormalize() {
    try {
        const missing = [];
        // Make sure all forms of normalization are supported
        ["NFD", "NFC", "NFKD", "NFKC"].forEach((form) => {
            try {
                if ("test".normalize(form) !== "test") {
                    throw new Error("bad normalize");
                }
                ;
            }
            catch (error) {
                missing.push(form);
            }
        });
        if (missing.length) {
            throw new Error("missing " + missing.join(", "));
        }
        if (String.fromCharCode(0xe9).normalize("NFD") !== String.fromCharCode(0x65, 0x0301)) {
            throw new Error("broken implementation");
        }
    }
    catch (error) {
        return error.message;
    }
    return null;
}
const _normalizeError = _checkNormalize();
var LogLevel;
(function (LogLevel) {
    LogLevel["DEBUG"] = "DEBUG";
    LogLevel["INFO"] = "INFO";
    LogLevel["WARNING"] = "WARNING";
    LogLevel["ERROR"] = "ERROR";
    LogLevel["OFF"] = "OFF";
})(LogLevel || (LogLevel = {}));
var ErrorCode;
(function (ErrorCode) {
    ///////////////////
    // Generic Errors
    // Unknown Error
    ErrorCode["UNKNOWN_ERROR"] = "UNKNOWN_ERROR";
    // Not Implemented
    ErrorCode["NOT_IMPLEMENTED"] = "NOT_IMPLEMENTED";
    // Unsupported Operation
    //   - operation
    ErrorCode["UNSUPPORTED_OPERATION"] = "UNSUPPORTED_OPERATION";
    // Network Error (i.e. Ethereum Network, such as an invalid chain ID)
    //   - event ("noNetwork" is not re-thrown in provider.ready; otherwise thrown)
    ErrorCode["NETWORK_ERROR"] = "NETWORK_ERROR";
    // Some sort of bad response from the server
    ErrorCode["SERVER_ERROR"] = "SERVER_ERROR";
    // Timeout
    ErrorCode["TIMEOUT"] = "TIMEOUT";
    ///////////////////
    // Operational  Errors
    // Buffer Overrun
    ErrorCode["BUFFER_OVERRUN"] = "BUFFER_OVERRUN";
    // Numeric Fault
    //   - operation: the operation being executed
    //   - fault: the reason this faulted
    ErrorCode["NUMERIC_FAULT"] = "NUMERIC_FAULT";
    ///////////////////
    // Argument Errors
    // Missing new operator to an object
    //  - name: The name of the class
    ErrorCode["MISSING_NEW"] = "MISSING_NEW";
    // Invalid argument (e.g. value is incompatible with type) to a function:
    //   - argument: The argument name that was invalid
    //   - value: The value of the argument
    ErrorCode["INVALID_ARGUMENT"] = "INVALID_ARGUMENT";
    // Missing argument to a function:
    //   - count: The number of arguments received
    //   - expectedCount: The number of arguments expected
    ErrorCode["MISSING_ARGUMENT"] = "MISSING_ARGUMENT";
    // Too many arguments
    //   - count: The number of arguments received
    //   - expectedCount: The number of arguments expected
    ErrorCode["UNEXPECTED_ARGUMENT"] = "UNEXPECTED_ARGUMENT";
    ///////////////////
    // Blockchain Errors
    // Call exception
    //  - transaction: the transaction
    //  - address?: the contract address
    //  - args?: The arguments passed into the function
    //  - method?: The Solidity method signature
    //  - errorSignature?: The EIP848 error signature
    //  - errorArgs?: The EIP848 error parameters
    //  - reason: The reason (only for EIP848 "Error(string)")
    ErrorCode["CALL_EXCEPTION"] = "CALL_EXCEPTION";
    // Insufficient funds (< value + gasLimit * gasPrice)
    //   - transaction: the transaction attempted
    ErrorCode["INSUFFICIENT_FUNDS"] = "INSUFFICIENT_FUNDS";
    // Nonce has already been used
    //   - transaction: the transaction attempted
    ErrorCode["NONCE_EXPIRED"] = "NONCE_EXPIRED";
    // The replacement fee for the transaction is too low
    //   - transaction: the transaction attempted
    ErrorCode["REPLACEMENT_UNDERPRICED"] = "REPLACEMENT_UNDERPRICED";
    // The gas limit could not be estimated
    //   - transaction: the transaction passed to estimateGas
    ErrorCode["UNPREDICTABLE_GAS_LIMIT"] = "UNPREDICTABLE_GAS_LIMIT";
    // The transaction was replaced by one with a higher gas price
    //   - reason: "cancelled", "replaced" or "repriced"
    //   - cancelled: true if reason == "cancelled" or reason == "replaced")
    //   - hash: original transaction hash
    //   - replacement: the full TransactionsResponse for the replacement
    //   - receipt: the receipt of the replacement
    ErrorCode["TRANSACTION_REPLACED"] = "TRANSACTION_REPLACED";
    ///////////////////
    // Interaction Errors
    // The user rejected the action, such as signing a message or sending
    // a transaction
    ErrorCode["ACTION_REJECTED"] = "ACTION_REJECTED";
})(ErrorCode || (ErrorCode = {}));
const HEX = "0123456789abcdef";
class Logger {
    constructor(version) {
        Object.defineProperty(this, "version", {
            enumerable: true,
            value: version,
            writable: false
        });
    }
    _log(logLevel, args) {
        const level = logLevel.toLowerCase();
        if (LogLevels[level] == null) {
            this.throwArgumentError("invalid log level name", "logLevel", logLevel);
        }
        if (_logLevel > LogLevels[level]) {
            return;
        }
        console.log.apply(console, args);
    }
    debug(...args) {
        this._log(Logger.levels.DEBUG, args);
    }
    info(...args) {
        this._log(Logger.levels.INFO, args);
    }
    warn(...args) {
        this._log(Logger.levels.WARNING, args);
    }
    makeError(message, code, params) {
        // Errors are being censored
        if (_censorErrors) {
            return this.makeError("censored error", code, {});
        }
        if (!code) {
            code = Logger.errors.UNKNOWN_ERROR;
        }
        if (!params) {
            params = {};
        }
        const messageDetails = [];
        Object.keys(params).forEach((key) => {
            const value = params[key];
            try {
                if (value instanceof Uint8Array) {
                    let hex = "";
                    for (let i = 0; i < value.length; i++) {
                        hex += HEX[value[i] >> 4];
                        hex += HEX[value[i] & 0x0f];
                    }
                    messageDetails.push(key + "=Uint8Array(0x" + hex + ")");
                }
                else {
                    messageDetails.push(key + "=" + JSON.stringify(value));
                }
            }
            catch (error) {
                messageDetails.push(key + "=" + JSON.stringify(params[key].toString()));
            }
        });
        messageDetails.push(`code=${code}`);
        messageDetails.push(`version=${this.version}`);
        const reason = message;
        let url = "";
        switch (code) {
            case ErrorCode.NUMERIC_FAULT: {
                url = "NUMERIC_FAULT";
                const fault = message;
                switch (fault) {
                    case "overflow":
                    case "underflow":
                    case "division-by-zero":
                        url += "-" + fault;
                        break;
                    case "negative-power":
                    case "negative-width":
                        url += "-unsupported";
                        break;
                    case "unbound-bitwise-result":
                        url += "-unbound-result";
                        break;
                }
                break;
            }
            case ErrorCode.CALL_EXCEPTION:
            case ErrorCode.INSUFFICIENT_FUNDS:
            case ErrorCode.MISSING_NEW:
            case ErrorCode.NONCE_EXPIRED:
            case ErrorCode.REPLACEMENT_UNDERPRICED:
            case ErrorCode.TRANSACTION_REPLACED:
            case ErrorCode.UNPREDICTABLE_GAS_LIMIT:
                url = code;
                break;
        }
        if (url) {
            message += " [ See: https:/\/links.ethers.org/v5-errors-" + url + " ]";
        }
        if (messageDetails.length) {
            message += " (" + messageDetails.join(", ") + ")";
        }
        // @TODO: Any??
        const error = new Error(message);
        error.reason = reason;
        error.code = code;
        Object.keys(params).forEach(function (key) {
            error[key] = params[key];
        });
        return error;
    }
    throwError(message, code, params) {
        throw this.makeError(message, code, params);
    }
    throwArgumentError(message, name, value) {
        return this.throwError(message, Logger.errors.INVALID_ARGUMENT, {
            argument: name,
            value: value
        });
    }
    assert(condition, message, code, params) {
        if (!!condition) {
            return;
        }
        this.throwError(message, code, params);
    }
    assertArgument(condition, message, name, value) {
        if (!!condition) {
            return;
        }
        this.throwArgumentError(message, name, value);
    }
    checkNormalize(message) {
        if (_normalizeError) {
            this.throwError("platform missing String.prototype.normalize", Logger.errors.UNSUPPORTED_OPERATION, {
                operation: "String.prototype.normalize", form: _normalizeError
            });
        }
    }
    checkSafeUint53(value, message) {
        if (typeof (value) !== "number") {
            return;
        }
        if (message == null) {
            message = "value not safe";
        }
        if (value < 0 || value >= 0x1fffffffffffff) {
            this.throwError(message, Logger.errors.NUMERIC_FAULT, {
                operation: "checkSafeInteger",
                fault: "out-of-safe-range",
                value: value
            });
        }
        if (value % 1) {
            this.throwError(message, Logger.errors.NUMERIC_FAULT, {
                operation: "checkSafeInteger",
                fault: "non-integer",
                value: value
            });
        }
    }
    checkArgumentCount(count, expectedCount, message) {
        if (message) {
            message = ": " + message;
        }
        else {
            message = "";
        }
        if (count < expectedCount) {
            this.throwError("missing argument" + message, Logger.errors.MISSING_ARGUMENT, {
                count: count,
                expectedCount: expectedCount
            });
        }
        if (count > expectedCount) {
            this.throwError("too many arguments" + message, Logger.errors.UNEXPECTED_ARGUMENT, {
                count: count,
                expectedCount: expectedCount
            });
        }
    }
    checkNew(target, kind) {
        if (target === Object || target == null) {
            this.throwError("missing new", Logger.errors.MISSING_NEW, { name: kind.name });
        }
    }
    checkAbstract(target, kind) {
        if (target === kind) {
            this.throwError("cannot instantiate abstract class " + JSON.stringify(kind.name) + " directly; use a sub-class", Logger.errors.UNSUPPORTED_OPERATION, { name: target.name, operation: "new" });
        }
        else if (target === Object || target == null) {
            this.throwError("missing new", Logger.errors.MISSING_NEW, { name: kind.name });
        }
    }
    static globalLogger() {
        if (!_globalLogger) {
            _globalLogger = new Logger(version$3);
        }
        return _globalLogger;
    }
    static setCensorship(censorship, permanent) {
        if (!censorship && permanent) {
            this.globalLogger().throwError("cannot permanently disable censorship", Logger.errors.UNSUPPORTED_OPERATION, {
                operation: "setCensorship"
            });
        }
        if (_permanentCensorErrors) {
            if (!censorship) {
                return;
            }
            this.globalLogger().throwError("error censorship permanent", Logger.errors.UNSUPPORTED_OPERATION, {
                operation: "setCensorship"
            });
        }
        _censorErrors = !!censorship;
        _permanentCensorErrors = !!permanent;
    }
    static setLogLevel(logLevel) {
        const level = LogLevels[logLevel.toLowerCase()];
        if (level == null) {
            Logger.globalLogger().warn("invalid log level - " + logLevel);
            return;
        }
        _logLevel = level;
    }
    static from(version) {
        return new Logger(version);
    }
}
Logger.errors = ErrorCode;
Logger.levels = LogLevel;

const version$2 = "bytes/5.7.0";

const logger$2 = new Logger(version$2);
///////////////////////////////
function isHexable(value) {
    return !!(value.toHexString);
}
function addSlice(array) {
    if (array.slice) {
        return array;
    }
    array.slice = function () {
        const args = Array.prototype.slice.call(arguments);
        return addSlice(new Uint8Array(Array.prototype.slice.apply(array, args)));
    };
    return array;
}
function isInteger(value) {
    return (typeof (value) === "number" && value == value && (value % 1) === 0);
}
function isBytes(value) {
    if (value == null) {
        return false;
    }
    if (value.constructor === Uint8Array) {
        return true;
    }
    if (typeof (value) === "string") {
        return false;
    }
    if (!isInteger(value.length) || value.length < 0) {
        return false;
    }
    for (let i = 0; i < value.length; i++) {
        const v = value[i];
        if (!isInteger(v) || v < 0 || v >= 256) {
            return false;
        }
    }
    return true;
}
function arrayify(value, options) {
    if (!options) {
        options = {};
    }
    if (typeof (value) === "number") {
        logger$2.checkSafeUint53(value, "invalid arrayify value");
        const result = [];
        while (value) {
            result.unshift(value & 0xff);
            value = parseInt(String(value / 256));
        }
        if (result.length === 0) {
            result.push(0);
        }
        return addSlice(new Uint8Array(result));
    }
    if (options.allowMissingPrefix && typeof (value) === "string" && value.substring(0, 2) !== "0x") {
        value = "0x" + value;
    }
    if (isHexable(value)) {
        value = value.toHexString();
    }
    if (isHexString(value)) {
        let hex = value.substring(2);
        if (hex.length % 2) {
            if (options.hexPad === "left") {
                hex = "0" + hex;
            }
            else if (options.hexPad === "right") {
                hex += "0";
            }
            else {
                logger$2.throwArgumentError("hex data is odd-length", "value", value);
            }
        }
        const result = [];
        for (let i = 0; i < hex.length; i += 2) {
            result.push(parseInt(hex.substring(i, i + 2), 16));
        }
        return addSlice(new Uint8Array(result));
    }
    if (isBytes(value)) {
        return addSlice(new Uint8Array(value));
    }
    return logger$2.throwArgumentError("invalid arrayify value", "value", value);
}
function zeroPad(value, length) {
    value = arrayify(value);
    if (value.length > length) {
        logger$2.throwArgumentError("value out of range", "value", arguments[0]);
    }
    const result = new Uint8Array(length);
    result.set(value, length - value.length);
    return addSlice(result);
}
function isHexString(value, length) {
    if (typeof (value) !== "string" || !value.match(/^0x[0-9A-Fa-f]*$/)) {
        return false;
    }
    if (length && value.length !== 2 + 2 * length) {
        return false;
    }
    return true;
}
const HexCharacters = "0123456789abcdef";
function hexlify(value, options) {
    if (!options) {
        options = {};
    }
    if (typeof (value) === "number") {
        logger$2.checkSafeUint53(value, "invalid hexlify value");
        let hex = "";
        while (value) {
            hex = HexCharacters[value & 0xf] + hex;
            value = Math.floor(value / 16);
        }
        if (hex.length) {
            if (hex.length % 2) {
                hex = "0" + hex;
            }
            return "0x" + hex;
        }
        return "0x00";
    }
    if (typeof (value) === "bigint") {
        value = value.toString(16);
        if (value.length % 2) {
            return ("0x0" + value);
        }
        return "0x" + value;
    }
    if (options.allowMissingPrefix && typeof (value) === "string" && value.substring(0, 2) !== "0x") {
        value = "0x" + value;
    }
    if (isHexable(value)) {
        return value.toHexString();
    }
    if (isHexString(value)) {
        if (value.length % 2) {
            if (options.hexPad === "left") {
                value = "0x0" + value.substring(2);
            }
            else if (options.hexPad === "right") {
                value += "0";
            }
            else {
                logger$2.throwArgumentError("hex data is odd-length", "value", value);
            }
        }
        return value.toLowerCase();
    }
    if (isBytes(value)) {
        let result = "0x";
        for (let i = 0; i < value.length; i++) {
            let v = value[i];
            result += HexCharacters[(v & 0xf0) >> 4] + HexCharacters[v & 0x0f];
        }
        return result;
    }
    return logger$2.throwArgumentError("invalid hexlify value", "value", value);
}

const version$1 = "bignumber/5.7.0";

var BN = _BN.BN;
const logger$1 = new Logger(version$1);
const _constructorGuard = {};
const MAX_SAFE = 0x1fffffffffffff;
// Only warn about passing 10 into radix once
let _warnedToStringRadix = false;
class BigNumber {
    constructor(constructorGuard, hex) {
        if (constructorGuard !== _constructorGuard) {
            logger$1.throwError("cannot call constructor directly; use BigNumber.from", Logger.errors.UNSUPPORTED_OPERATION, {
                operation: "new (BigNumber)"
            });
        }
        this._hex = hex;
        this._isBigNumber = true;
        Object.freeze(this);
    }
    fromTwos(value) {
        return toBigNumber(toBN(this).fromTwos(value));
    }
    toTwos(value) {
        return toBigNumber(toBN(this).toTwos(value));
    }
    abs() {
        if (this._hex[0] === "-") {
            return BigNumber.from(this._hex.substring(1));
        }
        return this;
    }
    add(other) {
        return toBigNumber(toBN(this).add(toBN(other)));
    }
    sub(other) {
        return toBigNumber(toBN(this).sub(toBN(other)));
    }
    div(other) {
        const o = BigNumber.from(other);
        if (o.isZero()) {
            throwFault("division-by-zero", "div");
        }
        return toBigNumber(toBN(this).div(toBN(other)));
    }
    mul(other) {
        return toBigNumber(toBN(this).mul(toBN(other)));
    }
    mod(other) {
        const value = toBN(other);
        if (value.isNeg()) {
            throwFault("division-by-zero", "mod");
        }
        return toBigNumber(toBN(this).umod(value));
    }
    pow(other) {
        const value = toBN(other);
        if (value.isNeg()) {
            throwFault("negative-power", "pow");
        }
        return toBigNumber(toBN(this).pow(value));
    }
    and(other) {
        const value = toBN(other);
        if (this.isNegative() || value.isNeg()) {
            throwFault("unbound-bitwise-result", "and");
        }
        return toBigNumber(toBN(this).and(value));
    }
    or(other) {
        const value = toBN(other);
        if (this.isNegative() || value.isNeg()) {
            throwFault("unbound-bitwise-result", "or");
        }
        return toBigNumber(toBN(this).or(value));
    }
    xor(other) {
        const value = toBN(other);
        if (this.isNegative() || value.isNeg()) {
            throwFault("unbound-bitwise-result", "xor");
        }
        return toBigNumber(toBN(this).xor(value));
    }
    mask(value) {
        if (this.isNegative() || value < 0) {
            throwFault("negative-width", "mask");
        }
        return toBigNumber(toBN(this).maskn(value));
    }
    shl(value) {
        if (this.isNegative() || value < 0) {
            throwFault("negative-width", "shl");
        }
        return toBigNumber(toBN(this).shln(value));
    }
    shr(value) {
        if (this.isNegative() || value < 0) {
            throwFault("negative-width", "shr");
        }
        return toBigNumber(toBN(this).shrn(value));
    }
    eq(other) {
        return toBN(this).eq(toBN(other));
    }
    lt(other) {
        return toBN(this).lt(toBN(other));
    }
    lte(other) {
        return toBN(this).lte(toBN(other));
    }
    gt(other) {
        return toBN(this).gt(toBN(other));
    }
    gte(other) {
        return toBN(this).gte(toBN(other));
    }
    isNegative() {
        return (this._hex[0] === "-");
    }
    isZero() {
        return toBN(this).isZero();
    }
    toNumber() {
        try {
            return toBN(this).toNumber();
        }
        catch (error) {
            throwFault("overflow", "toNumber", this.toString());
        }
        return null;
    }
    toBigInt() {
        try {
            return BigInt(this.toString());
        }
        catch (e) { }
        return logger$1.throwError("this platform does not support BigInt", Logger.errors.UNSUPPORTED_OPERATION, {
            value: this.toString()
        });
    }
    toString() {
        // Lots of people expect this, which we do not support, so check (See: #889)
        if (arguments.length > 0) {
            if (arguments[0] === 10) {
                if (!_warnedToStringRadix) {
                    _warnedToStringRadix = true;
                    logger$1.warn("BigNumber.toString does not accept any parameters; base-10 is assumed");
                }
            }
            else if (arguments[0] === 16) {
                logger$1.throwError("BigNumber.toString does not accept any parameters; use bigNumber.toHexString()", Logger.errors.UNEXPECTED_ARGUMENT, {});
            }
            else {
                logger$1.throwError("BigNumber.toString does not accept parameters", Logger.errors.UNEXPECTED_ARGUMENT, {});
            }
        }
        return toBN(this).toString(10);
    }
    toHexString() {
        return this._hex;
    }
    toJSON(key) {
        return { type: "BigNumber", hex: this.toHexString() };
    }
    static from(value) {
        if (value instanceof BigNumber) {
            return value;
        }
        if (typeof (value) === "string") {
            if (value.match(/^-?0x[0-9a-f]+$/i)) {
                return new BigNumber(_constructorGuard, toHex(value));
            }
            if (value.match(/^-?[0-9]+$/)) {
                return new BigNumber(_constructorGuard, toHex(new BN(value)));
            }
            return logger$1.throwArgumentError("invalid BigNumber string", "value", value);
        }
        if (typeof (value) === "number") {
            if (value % 1) {
                throwFault("underflow", "BigNumber.from", value);
            }
            if (value >= MAX_SAFE || value <= -MAX_SAFE) {
                throwFault("overflow", "BigNumber.from", value);
            }
            return BigNumber.from(String(value));
        }
        const anyValue = value;
        if (typeof (anyValue) === "bigint") {
            return BigNumber.from(anyValue.toString());
        }
        if (isBytes(anyValue)) {
            return BigNumber.from(hexlify(anyValue));
        }
        if (anyValue) {
            // Hexable interface (takes priority)
            if (anyValue.toHexString) {
                const hex = anyValue.toHexString();
                if (typeof (hex) === "string") {
                    return BigNumber.from(hex);
                }
            }
            else {
                // For now, handle legacy JSON-ified values (goes away in v6)
                let hex = anyValue._hex;
                // New-form JSON
                if (hex == null && anyValue.type === "BigNumber") {
                    hex = anyValue.hex;
                }
                if (typeof (hex) === "string") {
                    if (isHexString(hex) || (hex[0] === "-" && isHexString(hex.substring(1)))) {
                        return BigNumber.from(hex);
                    }
                }
            }
        }
        return logger$1.throwArgumentError("invalid BigNumber value", "value", value);
    }
    static isBigNumber(value) {
        return !!(value && value._isBigNumber);
    }
}
// Normalize the hex string
function toHex(value) {
    // For BN, call on the hex string
    if (typeof (value) !== "string") {
        return toHex(value.toString(16));
    }
    // If negative, prepend the negative sign to the normalized positive value
    if (value[0] === "-") {
        // Strip off the negative sign
        value = value.substring(1);
        // Cannot have multiple negative signs (e.g. "--0x04")
        if (value[0] === "-") {
            logger$1.throwArgumentError("invalid hex", "value", value);
        }
        // Call toHex on the positive component
        value = toHex(value);
        // Do not allow "-0x00"
        if (value === "0x00") {
            return value;
        }
        // Negate the value
        return "-" + value;
    }
    // Add a "0x" prefix if missing
    if (value.substring(0, 2) !== "0x") {
        value = "0x" + value;
    }
    // Normalize zero
    if (value === "0x") {
        return "0x00";
    }
    // Make the string even length
    if (value.length % 2) {
        value = "0x0" + value.substring(2);
    }
    // Trim to smallest even-length string
    while (value.length > 4 && value.substring(0, 4) === "0x00") {
        value = "0x" + value.substring(4);
    }
    return value;
}
function toBigNumber(value) {
    return BigNumber.from(toHex(value));
}
function toBN(value) {
    const hex = BigNumber.from(value).toHexString();
    if (hex[0] === "-") {
        return (new BN("-" + hex.substring(3), 16));
    }
    return new BN(hex.substring(2), 16);
}
function throwFault(fault, operation, value) {
    const params = { fault: fault, operation: operation };
    if (value != null) {
        params.value = value;
    }
    return logger$1.throwError(fault, Logger.errors.NUMERIC_FAULT, params);
}

var sha3$1 = {exports: {}};

/**
 * [js-sha3]{@link https://github.com/emn178/js-sha3}
 *
 * @version 0.8.0
 * @author Chen, Yi-Cyuan [emn178@gmail.com]
 * @copyright Chen, Yi-Cyuan 2015-2018
 * @license MIT
 */

(function (module) {
	/*jslint bitwise: true */
	(function () {

	  var INPUT_ERROR = 'input is invalid type';
	  var FINALIZE_ERROR = 'finalize already called';
	  var WINDOW = typeof window === 'object';
	  var root = WINDOW ? window : {};
	  if (root.JS_SHA3_NO_WINDOW) {
	    WINDOW = false;
	  }
	  var WEB_WORKER = !WINDOW && typeof self === 'object';
	  var NODE_JS = !root.JS_SHA3_NO_NODE_JS && typeof process === 'object' && process.versions && process.versions.node;
	  if (NODE_JS) {
	    root = commonjsGlobal;
	  } else if (WEB_WORKER) {
	    root = self;
	  }
	  var COMMON_JS = !root.JS_SHA3_NO_COMMON_JS && 'object' === 'object' && module.exports;
	  var ARRAY_BUFFER = !root.JS_SHA3_NO_ARRAY_BUFFER && typeof ArrayBuffer !== 'undefined';
	  var HEX_CHARS = '0123456789abcdef'.split('');
	  var SHAKE_PADDING = [31, 7936, 2031616, 520093696];
	  var CSHAKE_PADDING = [4, 1024, 262144, 67108864];
	  var KECCAK_PADDING = [1, 256, 65536, 16777216];
	  var PADDING = [6, 1536, 393216, 100663296];
	  var SHIFT = [0, 8, 16, 24];
	  var RC = [1, 0, 32898, 0, 32906, 2147483648, 2147516416, 2147483648, 32907, 0, 2147483649,
	    0, 2147516545, 2147483648, 32777, 2147483648, 138, 0, 136, 0, 2147516425, 0,
	    2147483658, 0, 2147516555, 0, 139, 2147483648, 32905, 2147483648, 32771,
	    2147483648, 32770, 2147483648, 128, 2147483648, 32778, 0, 2147483658, 2147483648,
	    2147516545, 2147483648, 32896, 2147483648, 2147483649, 0, 2147516424, 2147483648];
	  var BITS = [224, 256, 384, 512];
	  var SHAKE_BITS = [128, 256];
	  var OUTPUT_TYPES = ['hex', 'buffer', 'arrayBuffer', 'array', 'digest'];
	  var CSHAKE_BYTEPAD = {
	    '128': 168,
	    '256': 136
	  };

	  if (root.JS_SHA3_NO_NODE_JS || !Array.isArray) {
	    Array.isArray = function (obj) {
	      return Object.prototype.toString.call(obj) === '[object Array]';
	    };
	  }

	  if (ARRAY_BUFFER && (root.JS_SHA3_NO_ARRAY_BUFFER_IS_VIEW || !ArrayBuffer.isView)) {
	    ArrayBuffer.isView = function (obj) {
	      return typeof obj === 'object' && obj.buffer && obj.buffer.constructor === ArrayBuffer;
	    };
	  }

	  var createOutputMethod = function (bits, padding, outputType) {
	    return function (message) {
	      return new Keccak(bits, padding, bits).update(message)[outputType]();
	    };
	  };

	  var createShakeOutputMethod = function (bits, padding, outputType) {
	    return function (message, outputBits) {
	      return new Keccak(bits, padding, outputBits).update(message)[outputType]();
	    };
	  };

	  var createCshakeOutputMethod = function (bits, padding, outputType) {
	    return function (message, outputBits, n, s) {
	      return methods['cshake' + bits].update(message, outputBits, n, s)[outputType]();
	    };
	  };

	  var createKmacOutputMethod = function (bits, padding, outputType) {
	    return function (key, message, outputBits, s) {
	      return methods['kmac' + bits].update(key, message, outputBits, s)[outputType]();
	    };
	  };

	  var createOutputMethods = function (method, createMethod, bits, padding) {
	    for (var i = 0; i < OUTPUT_TYPES.length; ++i) {
	      var type = OUTPUT_TYPES[i];
	      method[type] = createMethod(bits, padding, type);
	    }
	    return method;
	  };

	  var createMethod = function (bits, padding) {
	    var method = createOutputMethod(bits, padding, 'hex');
	    method.create = function () {
	      return new Keccak(bits, padding, bits);
	    };
	    method.update = function (message) {
	      return method.create().update(message);
	    };
	    return createOutputMethods(method, createOutputMethod, bits, padding);
	  };

	  var createShakeMethod = function (bits, padding) {
	    var method = createShakeOutputMethod(bits, padding, 'hex');
	    method.create = function (outputBits) {
	      return new Keccak(bits, padding, outputBits);
	    };
	    method.update = function (message, outputBits) {
	      return method.create(outputBits).update(message);
	    };
	    return createOutputMethods(method, createShakeOutputMethod, bits, padding);
	  };

	  var createCshakeMethod = function (bits, padding) {
	    var w = CSHAKE_BYTEPAD[bits];
	    var method = createCshakeOutputMethod(bits, padding, 'hex');
	    method.create = function (outputBits, n, s) {
	      if (!n && !s) {
	        return methods['shake' + bits].create(outputBits);
	      } else {
	        return new Keccak(bits, padding, outputBits).bytepad([n, s], w);
	      }
	    };
	    method.update = function (message, outputBits, n, s) {
	      return method.create(outputBits, n, s).update(message);
	    };
	    return createOutputMethods(method, createCshakeOutputMethod, bits, padding);
	  };

	  var createKmacMethod = function (bits, padding) {
	    var w = CSHAKE_BYTEPAD[bits];
	    var method = createKmacOutputMethod(bits, padding, 'hex');
	    method.create = function (key, outputBits, s) {
	      return new Kmac(bits, padding, outputBits).bytepad(['KMAC', s], w).bytepad([key], w);
	    };
	    method.update = function (key, message, outputBits, s) {
	      return method.create(key, outputBits, s).update(message);
	    };
	    return createOutputMethods(method, createKmacOutputMethod, bits, padding);
	  };

	  var algorithms = [
	    { name: 'keccak', padding: KECCAK_PADDING, bits: BITS, createMethod: createMethod },
	    { name: 'sha3', padding: PADDING, bits: BITS, createMethod: createMethod },
	    { name: 'shake', padding: SHAKE_PADDING, bits: SHAKE_BITS, createMethod: createShakeMethod },
	    { name: 'cshake', padding: CSHAKE_PADDING, bits: SHAKE_BITS, createMethod: createCshakeMethod },
	    { name: 'kmac', padding: CSHAKE_PADDING, bits: SHAKE_BITS, createMethod: createKmacMethod }
	  ];

	  var methods = {}, methodNames = [];

	  for (var i = 0; i < algorithms.length; ++i) {
	    var algorithm = algorithms[i];
	    var bits = algorithm.bits;
	    for (var j = 0; j < bits.length; ++j) {
	      var methodName = algorithm.name + '_' + bits[j];
	      methodNames.push(methodName);
	      methods[methodName] = algorithm.createMethod(bits[j], algorithm.padding);
	      if (algorithm.name !== 'sha3') {
	        var newMethodName = algorithm.name + bits[j];
	        methodNames.push(newMethodName);
	        methods[newMethodName] = methods[methodName];
	      }
	    }
	  }

	  function Keccak(bits, padding, outputBits) {
	    this.blocks = [];
	    this.s = [];
	    this.padding = padding;
	    this.outputBits = outputBits;
	    this.reset = true;
	    this.finalized = false;
	    this.block = 0;
	    this.start = 0;
	    this.blockCount = (1600 - (bits << 1)) >> 5;
	    this.byteCount = this.blockCount << 2;
	    this.outputBlocks = outputBits >> 5;
	    this.extraBytes = (outputBits & 31) >> 3;

	    for (var i = 0; i < 50; ++i) {
	      this.s[i] = 0;
	    }
	  }

	  Keccak.prototype.update = function (message) {
	    if (this.finalized) {
	      throw new Error(FINALIZE_ERROR);
	    }
	    var notString, type = typeof message;
	    if (type !== 'string') {
	      if (type === 'object') {
	        if (message === null) {
	          throw new Error(INPUT_ERROR);
	        } else if (ARRAY_BUFFER && message.constructor === ArrayBuffer) {
	          message = new Uint8Array(message);
	        } else if (!Array.isArray(message)) {
	          if (!ARRAY_BUFFER || !ArrayBuffer.isView(message)) {
	            throw new Error(INPUT_ERROR);
	          }
	        }
	      } else {
	        throw new Error(INPUT_ERROR);
	      }
	      notString = true;
	    }
	    var blocks = this.blocks, byteCount = this.byteCount, length = message.length,
	      blockCount = this.blockCount, index = 0, s = this.s, i, code;

	    while (index < length) {
	      if (this.reset) {
	        this.reset = false;
	        blocks[0] = this.block;
	        for (i = 1; i < blockCount + 1; ++i) {
	          blocks[i] = 0;
	        }
	      }
	      if (notString) {
	        for (i = this.start; index < length && i < byteCount; ++index) {
	          blocks[i >> 2] |= message[index] << SHIFT[i++ & 3];
	        }
	      } else {
	        for (i = this.start; index < length && i < byteCount; ++index) {
	          code = message.charCodeAt(index);
	          if (code < 0x80) {
	            blocks[i >> 2] |= code << SHIFT[i++ & 3];
	          } else if (code < 0x800) {
	            blocks[i >> 2] |= (0xc0 | (code >> 6)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          } else if (code < 0xd800 || code >= 0xe000) {
	            blocks[i >> 2] |= (0xe0 | (code >> 12)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          } else {
	            code = 0x10000 + (((code & 0x3ff) << 10) | (message.charCodeAt(++index) & 0x3ff));
	            blocks[i >> 2] |= (0xf0 | (code >> 18)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 12) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          }
	        }
	      }
	      this.lastByteIndex = i;
	      if (i >= byteCount) {
	        this.start = i - byteCount;
	        this.block = blocks[blockCount];
	        for (i = 0; i < blockCount; ++i) {
	          s[i] ^= blocks[i];
	        }
	        f(s);
	        this.reset = true;
	      } else {
	        this.start = i;
	      }
	    }
	    return this;
	  };

	  Keccak.prototype.encode = function (x, right) {
	    var o = x & 255, n = 1;
	    var bytes = [o];
	    x = x >> 8;
	    o = x & 255;
	    while (o > 0) {
	      bytes.unshift(o);
	      x = x >> 8;
	      o = x & 255;
	      ++n;
	    }
	    if (right) {
	      bytes.push(n);
	    } else {
	      bytes.unshift(n);
	    }
	    this.update(bytes);
	    return bytes.length;
	  };

	  Keccak.prototype.encodeString = function (str) {
	    var notString, type = typeof str;
	    if (type !== 'string') {
	      if (type === 'object') {
	        if (str === null) {
	          throw new Error(INPUT_ERROR);
	        } else if (ARRAY_BUFFER && str.constructor === ArrayBuffer) {
	          str = new Uint8Array(str);
	        } else if (!Array.isArray(str)) {
	          if (!ARRAY_BUFFER || !ArrayBuffer.isView(str)) {
	            throw new Error(INPUT_ERROR);
	          }
	        }
	      } else {
	        throw new Error(INPUT_ERROR);
	      }
	      notString = true;
	    }
	    var bytes = 0, length = str.length;
	    if (notString) {
	      bytes = length;
	    } else {
	      for (var i = 0; i < str.length; ++i) {
	        var code = str.charCodeAt(i);
	        if (code < 0x80) {
	          bytes += 1;
	        } else if (code < 0x800) {
	          bytes += 2;
	        } else if (code < 0xd800 || code >= 0xe000) {
	          bytes += 3;
	        } else {
	          code = 0x10000 + (((code & 0x3ff) << 10) | (str.charCodeAt(++i) & 0x3ff));
	          bytes += 4;
	        }
	      }
	    }
	    bytes += this.encode(bytes * 8);
	    this.update(str);
	    return bytes;
	  };

	  Keccak.prototype.bytepad = function (strs, w) {
	    var bytes = this.encode(w);
	    for (var i = 0; i < strs.length; ++i) {
	      bytes += this.encodeString(strs[i]);
	    }
	    var paddingBytes = w - bytes % w;
	    var zeros = [];
	    zeros.length = paddingBytes;
	    this.update(zeros);
	    return this;
	  };

	  Keccak.prototype.finalize = function () {
	    if (this.finalized) {
	      return;
	    }
	    this.finalized = true;
	    var blocks = this.blocks, i = this.lastByteIndex, blockCount = this.blockCount, s = this.s;
	    blocks[i >> 2] |= this.padding[i & 3];
	    if (this.lastByteIndex === this.byteCount) {
	      blocks[0] = blocks[blockCount];
	      for (i = 1; i < blockCount + 1; ++i) {
	        blocks[i] = 0;
	      }
	    }
	    blocks[blockCount - 1] |= 0x80000000;
	    for (i = 0; i < blockCount; ++i) {
	      s[i] ^= blocks[i];
	    }
	    f(s);
	  };

	  Keccak.prototype.toString = Keccak.prototype.hex = function () {
	    this.finalize();

	    var blockCount = this.blockCount, s = this.s, outputBlocks = this.outputBlocks,
	      extraBytes = this.extraBytes, i = 0, j = 0;
	    var hex = '', block;
	    while (j < outputBlocks) {
	      for (i = 0; i < blockCount && j < outputBlocks; ++i, ++j) {
	        block = s[i];
	        hex += HEX_CHARS[(block >> 4) & 0x0F] + HEX_CHARS[block & 0x0F] +
	          HEX_CHARS[(block >> 12) & 0x0F] + HEX_CHARS[(block >> 8) & 0x0F] +
	          HEX_CHARS[(block >> 20) & 0x0F] + HEX_CHARS[(block >> 16) & 0x0F] +
	          HEX_CHARS[(block >> 28) & 0x0F] + HEX_CHARS[(block >> 24) & 0x0F];
	      }
	      if (j % blockCount === 0) {
	        f(s);
	        i = 0;
	      }
	    }
	    if (extraBytes) {
	      block = s[i];
	      hex += HEX_CHARS[(block >> 4) & 0x0F] + HEX_CHARS[block & 0x0F];
	      if (extraBytes > 1) {
	        hex += HEX_CHARS[(block >> 12) & 0x0F] + HEX_CHARS[(block >> 8) & 0x0F];
	      }
	      if (extraBytes > 2) {
	        hex += HEX_CHARS[(block >> 20) & 0x0F] + HEX_CHARS[(block >> 16) & 0x0F];
	      }
	    }
	    return hex;
	  };

	  Keccak.prototype.arrayBuffer = function () {
	    this.finalize();

	    var blockCount = this.blockCount, s = this.s, outputBlocks = this.outputBlocks,
	      extraBytes = this.extraBytes, i = 0, j = 0;
	    var bytes = this.outputBits >> 3;
	    var buffer;
	    if (extraBytes) {
	      buffer = new ArrayBuffer((outputBlocks + 1) << 2);
	    } else {
	      buffer = new ArrayBuffer(bytes);
	    }
	    var array = new Uint32Array(buffer);
	    while (j < outputBlocks) {
	      for (i = 0; i < blockCount && j < outputBlocks; ++i, ++j) {
	        array[j] = s[i];
	      }
	      if (j % blockCount === 0) {
	        f(s);
	      }
	    }
	    if (extraBytes) {
	      array[i] = s[i];
	      buffer = buffer.slice(0, bytes);
	    }
	    return buffer;
	  };

	  Keccak.prototype.buffer = Keccak.prototype.arrayBuffer;

	  Keccak.prototype.digest = Keccak.prototype.array = function () {
	    this.finalize();

	    var blockCount = this.blockCount, s = this.s, outputBlocks = this.outputBlocks,
	      extraBytes = this.extraBytes, i = 0, j = 0;
	    var array = [], offset, block;
	    while (j < outputBlocks) {
	      for (i = 0; i < blockCount && j < outputBlocks; ++i, ++j) {
	        offset = j << 2;
	        block = s[i];
	        array[offset] = block & 0xFF;
	        array[offset + 1] = (block >> 8) & 0xFF;
	        array[offset + 2] = (block >> 16) & 0xFF;
	        array[offset + 3] = (block >> 24) & 0xFF;
	      }
	      if (j % blockCount === 0) {
	        f(s);
	      }
	    }
	    if (extraBytes) {
	      offset = j << 2;
	      block = s[i];
	      array[offset] = block & 0xFF;
	      if (extraBytes > 1) {
	        array[offset + 1] = (block >> 8) & 0xFF;
	      }
	      if (extraBytes > 2) {
	        array[offset + 2] = (block >> 16) & 0xFF;
	      }
	    }
	    return array;
	  };

	  function Kmac(bits, padding, outputBits) {
	    Keccak.call(this, bits, padding, outputBits);
	  }

	  Kmac.prototype = new Keccak();

	  Kmac.prototype.finalize = function () {
	    this.encode(this.outputBits, true);
	    return Keccak.prototype.finalize.call(this);
	  };

	  var f = function (s) {
	    var h, l, n, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
	      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
	      b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33,
	      b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49;
	    for (n = 0; n < 48; n += 2) {
	      c0 = s[0] ^ s[10] ^ s[20] ^ s[30] ^ s[40];
	      c1 = s[1] ^ s[11] ^ s[21] ^ s[31] ^ s[41];
	      c2 = s[2] ^ s[12] ^ s[22] ^ s[32] ^ s[42];
	      c3 = s[3] ^ s[13] ^ s[23] ^ s[33] ^ s[43];
	      c4 = s[4] ^ s[14] ^ s[24] ^ s[34] ^ s[44];
	      c5 = s[5] ^ s[15] ^ s[25] ^ s[35] ^ s[45];
	      c6 = s[6] ^ s[16] ^ s[26] ^ s[36] ^ s[46];
	      c7 = s[7] ^ s[17] ^ s[27] ^ s[37] ^ s[47];
	      c8 = s[8] ^ s[18] ^ s[28] ^ s[38] ^ s[48];
	      c9 = s[9] ^ s[19] ^ s[29] ^ s[39] ^ s[49];

	      h = c8 ^ ((c2 << 1) | (c3 >>> 31));
	      l = c9 ^ ((c3 << 1) | (c2 >>> 31));
	      s[0] ^= h;
	      s[1] ^= l;
	      s[10] ^= h;
	      s[11] ^= l;
	      s[20] ^= h;
	      s[21] ^= l;
	      s[30] ^= h;
	      s[31] ^= l;
	      s[40] ^= h;
	      s[41] ^= l;
	      h = c0 ^ ((c4 << 1) | (c5 >>> 31));
	      l = c1 ^ ((c5 << 1) | (c4 >>> 31));
	      s[2] ^= h;
	      s[3] ^= l;
	      s[12] ^= h;
	      s[13] ^= l;
	      s[22] ^= h;
	      s[23] ^= l;
	      s[32] ^= h;
	      s[33] ^= l;
	      s[42] ^= h;
	      s[43] ^= l;
	      h = c2 ^ ((c6 << 1) | (c7 >>> 31));
	      l = c3 ^ ((c7 << 1) | (c6 >>> 31));
	      s[4] ^= h;
	      s[5] ^= l;
	      s[14] ^= h;
	      s[15] ^= l;
	      s[24] ^= h;
	      s[25] ^= l;
	      s[34] ^= h;
	      s[35] ^= l;
	      s[44] ^= h;
	      s[45] ^= l;
	      h = c4 ^ ((c8 << 1) | (c9 >>> 31));
	      l = c5 ^ ((c9 << 1) | (c8 >>> 31));
	      s[6] ^= h;
	      s[7] ^= l;
	      s[16] ^= h;
	      s[17] ^= l;
	      s[26] ^= h;
	      s[27] ^= l;
	      s[36] ^= h;
	      s[37] ^= l;
	      s[46] ^= h;
	      s[47] ^= l;
	      h = c6 ^ ((c0 << 1) | (c1 >>> 31));
	      l = c7 ^ ((c1 << 1) | (c0 >>> 31));
	      s[8] ^= h;
	      s[9] ^= l;
	      s[18] ^= h;
	      s[19] ^= l;
	      s[28] ^= h;
	      s[29] ^= l;
	      s[38] ^= h;
	      s[39] ^= l;
	      s[48] ^= h;
	      s[49] ^= l;

	      b0 = s[0];
	      b1 = s[1];
	      b32 = (s[11] << 4) | (s[10] >>> 28);
	      b33 = (s[10] << 4) | (s[11] >>> 28);
	      b14 = (s[20] << 3) | (s[21] >>> 29);
	      b15 = (s[21] << 3) | (s[20] >>> 29);
	      b46 = (s[31] << 9) | (s[30] >>> 23);
	      b47 = (s[30] << 9) | (s[31] >>> 23);
	      b28 = (s[40] << 18) | (s[41] >>> 14);
	      b29 = (s[41] << 18) | (s[40] >>> 14);
	      b20 = (s[2] << 1) | (s[3] >>> 31);
	      b21 = (s[3] << 1) | (s[2] >>> 31);
	      b2 = (s[13] << 12) | (s[12] >>> 20);
	      b3 = (s[12] << 12) | (s[13] >>> 20);
	      b34 = (s[22] << 10) | (s[23] >>> 22);
	      b35 = (s[23] << 10) | (s[22] >>> 22);
	      b16 = (s[33] << 13) | (s[32] >>> 19);
	      b17 = (s[32] << 13) | (s[33] >>> 19);
	      b48 = (s[42] << 2) | (s[43] >>> 30);
	      b49 = (s[43] << 2) | (s[42] >>> 30);
	      b40 = (s[5] << 30) | (s[4] >>> 2);
	      b41 = (s[4] << 30) | (s[5] >>> 2);
	      b22 = (s[14] << 6) | (s[15] >>> 26);
	      b23 = (s[15] << 6) | (s[14] >>> 26);
	      b4 = (s[25] << 11) | (s[24] >>> 21);
	      b5 = (s[24] << 11) | (s[25] >>> 21);
	      b36 = (s[34] << 15) | (s[35] >>> 17);
	      b37 = (s[35] << 15) | (s[34] >>> 17);
	      b18 = (s[45] << 29) | (s[44] >>> 3);
	      b19 = (s[44] << 29) | (s[45] >>> 3);
	      b10 = (s[6] << 28) | (s[7] >>> 4);
	      b11 = (s[7] << 28) | (s[6] >>> 4);
	      b42 = (s[17] << 23) | (s[16] >>> 9);
	      b43 = (s[16] << 23) | (s[17] >>> 9);
	      b24 = (s[26] << 25) | (s[27] >>> 7);
	      b25 = (s[27] << 25) | (s[26] >>> 7);
	      b6 = (s[36] << 21) | (s[37] >>> 11);
	      b7 = (s[37] << 21) | (s[36] >>> 11);
	      b38 = (s[47] << 24) | (s[46] >>> 8);
	      b39 = (s[46] << 24) | (s[47] >>> 8);
	      b30 = (s[8] << 27) | (s[9] >>> 5);
	      b31 = (s[9] << 27) | (s[8] >>> 5);
	      b12 = (s[18] << 20) | (s[19] >>> 12);
	      b13 = (s[19] << 20) | (s[18] >>> 12);
	      b44 = (s[29] << 7) | (s[28] >>> 25);
	      b45 = (s[28] << 7) | (s[29] >>> 25);
	      b26 = (s[38] << 8) | (s[39] >>> 24);
	      b27 = (s[39] << 8) | (s[38] >>> 24);
	      b8 = (s[48] << 14) | (s[49] >>> 18);
	      b9 = (s[49] << 14) | (s[48] >>> 18);

	      s[0] = b0 ^ (~b2 & b4);
	      s[1] = b1 ^ (~b3 & b5);
	      s[10] = b10 ^ (~b12 & b14);
	      s[11] = b11 ^ (~b13 & b15);
	      s[20] = b20 ^ (~b22 & b24);
	      s[21] = b21 ^ (~b23 & b25);
	      s[30] = b30 ^ (~b32 & b34);
	      s[31] = b31 ^ (~b33 & b35);
	      s[40] = b40 ^ (~b42 & b44);
	      s[41] = b41 ^ (~b43 & b45);
	      s[2] = b2 ^ (~b4 & b6);
	      s[3] = b3 ^ (~b5 & b7);
	      s[12] = b12 ^ (~b14 & b16);
	      s[13] = b13 ^ (~b15 & b17);
	      s[22] = b22 ^ (~b24 & b26);
	      s[23] = b23 ^ (~b25 & b27);
	      s[32] = b32 ^ (~b34 & b36);
	      s[33] = b33 ^ (~b35 & b37);
	      s[42] = b42 ^ (~b44 & b46);
	      s[43] = b43 ^ (~b45 & b47);
	      s[4] = b4 ^ (~b6 & b8);
	      s[5] = b5 ^ (~b7 & b9);
	      s[14] = b14 ^ (~b16 & b18);
	      s[15] = b15 ^ (~b17 & b19);
	      s[24] = b24 ^ (~b26 & b28);
	      s[25] = b25 ^ (~b27 & b29);
	      s[34] = b34 ^ (~b36 & b38);
	      s[35] = b35 ^ (~b37 & b39);
	      s[44] = b44 ^ (~b46 & b48);
	      s[45] = b45 ^ (~b47 & b49);
	      s[6] = b6 ^ (~b8 & b0);
	      s[7] = b7 ^ (~b9 & b1);
	      s[16] = b16 ^ (~b18 & b10);
	      s[17] = b17 ^ (~b19 & b11);
	      s[26] = b26 ^ (~b28 & b20);
	      s[27] = b27 ^ (~b29 & b21);
	      s[36] = b36 ^ (~b38 & b30);
	      s[37] = b37 ^ (~b39 & b31);
	      s[46] = b46 ^ (~b48 & b40);
	      s[47] = b47 ^ (~b49 & b41);
	      s[8] = b8 ^ (~b0 & b2);
	      s[9] = b9 ^ (~b1 & b3);
	      s[18] = b18 ^ (~b10 & b12);
	      s[19] = b19 ^ (~b11 & b13);
	      s[28] = b28 ^ (~b20 & b22);
	      s[29] = b29 ^ (~b21 & b23);
	      s[38] = b38 ^ (~b30 & b32);
	      s[39] = b39 ^ (~b31 & b33);
	      s[48] = b48 ^ (~b40 & b42);
	      s[49] = b49 ^ (~b41 & b43);

	      s[0] ^= RC[n];
	      s[1] ^= RC[n + 1];
	    }
	  };

	  if (COMMON_JS) {
	    module.exports = methods;
	  } else {
	    for (i = 0; i < methodNames.length; ++i) {
	      root[methodNames[i]] = methods[methodNames[i]];
	    }
	  }
	})(); 
} (sha3$1));

var sha3Exports = sha3$1.exports;
var sha3 = /*@__PURE__*/getDefaultExportFromCjs(sha3Exports);

function keccak256(data) {
    return '0x' + sha3.keccak_256(arrayify(data));
}

/**
 * @module @semaphore-protocol/group
 * @version 3.10.1
 * @file A library to create and manage Semaphore groups.
 * @copyright Ethereum Foundation 2022
 * @license MIT
 * @see [Github]{@link https://github.com/semaphore-protocol/semaphore/tree/main/packages/group}
*/

var poseidon2$1$1 = {};

const F$2 = BigInt('21888242871839275222246405745257275088548364400416034343698204186575808495617');
const N_ROUNDS_F$2 = 8;
const N_ROUNDS_P$2 = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
const pow5$2 = v => {
  let o = v * v;
  return v * o * o % F$2;
};
function mix$2(state, M) {
  const out = [];
  for (let x = 0; x < state.length; x++) {
    let o = 0n;
    for (let y = 0; y < state.length; y++) {
      o = o + M[x][y] * state[y];
    }
    out.push(o % F$2);
  }
  return out;
}
function poseidon$2(_inputs, opt) {
  const inputs = _inputs.map(i => BigInt(i));
  if (inputs.length <= 0) {
    throw new Error('poseidon-lite: Not enough inputs');
  }
  if (inputs.length > N_ROUNDS_P$2.length) {
    throw new Error('poseidon-lite: Too many inputs');
  }
  const t = inputs.length + 1;
  const nRoundsF = N_ROUNDS_F$2;
  const nRoundsP = N_ROUNDS_P$2[t - 2];
  const {
    C,
    M
  } = opt;
  if (M.length !== t) {
    throw new Error(`poseidon-lite: Incorrect M length, expected ${t} got ${M.length}`);
  }
  let state = [0n, ...inputs];
  for (let x = 0; x < nRoundsF + nRoundsP; x++) {
    for (let y = 0; y < state.length; y++) {
      state[y] = state[y] + C[x * t + y];
      if (x < nRoundsF / 2 || x >= nRoundsF / 2 + nRoundsP) state[y] = pow5$2(state[y]);else if (y === 0) state[y] = pow5$2(state[y]);
    }
    state = mix$2(state, M);
  }
  return state[0];
}
var poseidon_1$2 = poseidon$2;

var unstringify$2 = {};

Object.defineProperty(unstringify$2, "__esModule", {
  value: true
});
unstringify$2.default = unstringifyBigInts$2;
function unstringifyBigInts$2(o) {
  if (Array.isArray(o)) {
    return o.map(unstringifyBigInts$2);
  } else if (typeof o == 'object') {
    const res = {};
    for (const [key, val] of Object.entries(o)) {
      res[key] = unstringifyBigInts$2(val);
    }
    return res;
  }
  const byteArray = Uint8Array.from(atob(o), c => c.charCodeAt(0));
  const hex = [...byteArray].map(x => x.toString(16).padStart(2, '0')).join('');
  return BigInt(`0x${hex}`);
}

var _2$2 = {};

Object.defineProperty(_2$2, "__esModule", {
  value: true
});
_2$2.default = void 0;
var _default$4 = {
  C: ['DumlkrqalRjQWYbWVvQMIRTEmTwRuymTjSHUcwTNjm4=', 'APFEUjXyFIxZhlhxafwbzYh7CNTQCGjfVpb/9AlW6GQ=', 'CN/zSH6KyZ4fKaBY0PqAuTDHKHMLerNs6HnziQ7Pc/U=', 'Lye+aQ/a7kbDzij3UysTyFbDU0LIS9puIJZjEPrcAdA=', 'KyrhrPaLe40kFr6/PU9iNLdj/gS4BD7ki4MnvryhbPI=', 'AxnQYgcr737MperAb5fU1VlSwXWrawPq5ktEx9vxHPo=', 'KIE9yuuuqoKKN234evSmO8i3vyetScYpjvezh78oUm0=', 'JydnOyzLyQPxgb844cHUDSAzhlIAw1K8FQkord35y3g=', 'I07EXKJ3J8LnSr0rKhSUzW771D40BYfWuPueMeZcxjI=', 'FbUlNAMa4Y9/hiyyz3z3YKsQqBUKM3sczZn/boeX1Cg=', 'Dcj61tnks19e2aPRhrec444Oio0bWLEy1wHU7s9o0fY=', 'G82V/8IR+8pgD3BfrT+1Z+pOs3j2Lh/sl4BVGKR+TZw=', 'EFILCrchyt/p7/gbAW/DTcdto2wleJN4F8uXjQad5Vk=', 'H21IFJuOf32bJX2O1fu69CkySYB1/tCs6IqeuB9WJ/Y=', 'HZZV9lIwkBTSngDvNaIIm//43ByBbw3JyjS9tUYMhwU=', 'BN9aVv+VvK+wUfexzUOpm6cx/2fkcDIFj+PUGFaXzH0=', 'BnLZlfj/9kAVGz0pDO2vFIaQoQqMhCSn9uwoK25L6Cg=', 'CZlStBSIRFSyEgDX/6/dXwyancwG8nCOn8HYIJtcdbk=', 'BSy6IlXf0Ax8SDFDuo1GlEjkNYaptM2Rg/0OhDprn6Y=', 'C4ut7mkK246wvXRxK3mZr4LeVXByUa13Fgd8uTxGTdw=', 'EZsVkPEzB69aHuZRAgwHx0nBXWBoOoBQuWPQqOSyvdE=', 'AxULfNbV0XslKdNr4PZ7gyxKz8iE707lzhW+C/tKjQk=', 'LMYYLF4UVG488ZUfFzkSNVN077g9gImKvmnLMXyepWU=', 'AFAyVR5jeMRQz+EppASzdkIYyt7awU4rktLNcxEb8Pk=', 'IzI34yibqjS7FH6XLry5UWRpw5n8wGn7iPnaLMKCdrU=', 'Bcj09OvUpuPJgNMWdL++YyMDfyGzSuWk6AwtTCTWAoA=', 'CnsdsTBC05a6BdgYoxnyUlK8817zru2R7h8JslkPxls=', 'KnO3H5shDPWxQpZXLJ0y2/FW4rCG/0fcXfVCNlpATsA=', 'GsmwQXq8yaGTUQfp/8kdw+wY8sTb5/Ipdqdgu1xQxGA=', 'EsAzmuCDdII/q7B2cH70eSafPk1ssQQ0kBXuBG3JP8A=', 'C3R1sQKhZa1/WxjbTh5wT1KQCqMlO6rGgkZoLlbpoo4=', 'A3woSeGRyj7bHF5J9ui4kXyEPjeTZvLqMqs6qI1/hEg=', 'BaaBH4VW8BTpJnRmHiF+m9UgbFyToH3BRf2xdqcWNG8=', 'KaeV59mAKJRulHt11U6fBEB26Hp7KIO0e2de9fOL1m4=', 'IEOaDISzIutFo4V6/Bj1gm6Mc4LIoVhcUHvhmZgf0i8=', 'Lguo2U2ez0qU7CBQxzcf8btQ8neZqEttSipvKgmCyIc=', 'FD/RFc4I+yfKOOt8zoIrRReCLNIQkEjS5tDdzKF9ccg=', 'DGTL7LHHNLhXlo273PgTzfhhFlkyPby/yEMjYjvpyvE=', 'AoowWEfGg/ZG/KklwWP/WudPNI1iwrZw8UJs75QD2lM=', 'Lk71EP8Lb9pfqUCrTEOA8mpry2TYlCe4JNZ1W1254ww=', 'AIHJW8QzhOZj15JwyVbOO4kltPbQM7B4uWOE9QV5QA4=', 'LtXwyRy9l0kYfi+t5ofgXuJJGzScA5oLuoqfQCOguzg=', 'MFCZkfiNo1BLvzdO1ari8DRIoix2I0yMmQ8B8zpzUgY=', 'HD8g/VVAmlMiG3xNSaNWufChEZ+yBntBp1KQlEJOxq0=', 'ELTn86td8AMElRRFm24Y7sRrsiE+jhMeFwiHtH3cuWw=', 'KhmCl5w/9/Q93VQ9iRwqvd2A+ATAd9d1A5qjUC5Dre8=', 'HHTuZPFeHbb+3b6tVtbVXbpDHrw5bJr5XK0PExW9XJE=', 'B1M+yFC6f5jquTA8rOAbS55PLouCcIz6nC/kWgrhRqA=', 'IVdrQ45QBEmhUeTurxexVChcaPQtQsGAihGr83ZMB1A=', 'LxfAVZuP55YIrVyhk9YvELzoOEyBXwkGdD1pMINtSp4=', 'LUd+OGLQdwinnoqulGFwvJd1pCATGEdK5mWwsbficw4=', 'Fi9SQ5ZwZMOQ4JVXeYTyka+6ImbDj1q82Jvg9bJ0fqs=', 'K0yyM+3pukgmTs0siuUNGteoWWqH8p+Kd3enAJI5MxE=', 'LI+8st2Fc9wduvj0YihUd22y7s5thcTPQlTnw14DsHo=', 'HW80dyXkgWry/0U/DNVrGZ4bYen2Aemt5eiNuHCUnak=', 'IEsMOX9OvnHrwtiz31uRPfnmrAK2jTEyTNSa9cRWVSk=', 'DEy53DxP2BdPEUmzxjw8L57LgnzX3CVTT/j7dbx5xQI=', 'F0rWGhRIyJmiVBZHT0kwMB5cSUdSeeBjmmFt3EW8e1Q=', 'GpYXe89NjYn3Wd9OwvPN4uqqKMF3zA+hOpgW1Jo40u8=', 'Bm0EskMx1xzQ74BUvGDE/wUgLBJqIzwagkKs42C4owo=', 'KkxPxuwLDPUhlXgoccbdOzgcxl9y4CrVJwN6Yqob2AQ=', 'E6stE2zPN9RH6fLhSnztyV5yf4RG9tnX5Vr8ASGf1kk=', 'ESFVL8omBhYZ0k2EPcgnacGwT87Cb1UZTC4+hprMapo=', 'AO9lMyKxPWyIm8gXFcN9d6bNJn1ZXEqJCaVUbHyXz/E=', 'DiVIPkWmZSCLJh2Lp0BR5kAMd21lJZXZhFrKNdijl9M=', 'KfU23LnddoIkUmRlnhXYjjlaw9Td6S2MRkSNuXnuuok=', 'KlbvnyxT/rrf2jNXXb29iFoSTieAu+oXDkVrqs4Ppb4=', 'HINhx461z13s+3otF7XECfKuKZmkZ2Lo7kFiQKjLmvE=', 'FRr/XziyCg/ARzCJqvAga4Po5op2RQe/09CrS+dDGcU=', 'BMYYfkHtiB3BsjnIj3+dQ6n1L8jIts3R525HYVtR8QA=', 'E7N72A9NJ/sQ2EMx9vttU0uBxh7RV3ZEnoAbfdycKWc=', 'AaXFNic8LZ31eL+9MsF7eizjZkwqUgMskyHOscToqOQ=', 'KrNWGDTKc4Na0F9desuVC0qaLGZrlybagyI5Blt8OwI=', 'HU2OwpHnINsgD+bWhsDWE6yvavTpXTv2n37VFqWXtkY=', 'BBKU0sxITSKPV4T+eRn9K7klNRJAoEtxFRTJyAtlrx0=', 'FUrJjgFwjGEcT6cVmR8ASJj1eTnRJuOSBClx3ZDoH8Y=', 'CzOdisyn1Pg+7dhAk671EFCzaEyI+LCwRSRWO8bqTaQ=', 'CVXknmYQyUJUpPhM+6s0RZjw5x6v9Kfdge2VtQg5yC4=', 'BnRqYVbrpUQmueIiBvFavKmm9B5vU1xvNSVAHqBlRiY=', 'Dxj1oOzRQjxJbzggxUnCeDjleQ4r0KGWrJF8f/Mgd/s=', 'BPbuyhdR9zCKxZ7/W+smHku1Y1g+3nvJKnOCI9b3bhM=', 'K1aXM2TExPXBo+xNo83OA4gR6xFvs+RbwXaNJvwLN1g=', 'Ejdp3UnVsFTc12uJgEsby44TkrOFcWpdg/62XUN/Ke8=', 'IUe0JPxIyAqI7lK5EWmqzqmJ9kRkcRUJlCV7L7AcY+k=', 'D9wfWFSLhXAabFUF6jMqKWR+bzStQkPC6lStiXzr5U0=', 'Ejc6glH+oATfaKvPD3eG1Lzv8oxdu+DDlE9oXMCgsfI=', 'IeT06l81+FutfqUv90LJ6KZCdWtq9EID3YofNcGpADU=', 'FiQ5FtadLKPftHIiJNTEYrVzZkkvRekNioGTTxvDsUc=', 'HvvkbdeleLT2b5rbyItDeKvCFWbhoEU8oTpBWcrASsI=', 'B+pehTfPXdCIhgIOI6fzh9Ro1VJb5m+FO2csyWqIlpo=', 'BajE+ZaLiqO3tHijD5pbY2UPGadefOEcqf4WwLdsALw=', 'IPBXcSzCFlT7/lm9NF6NrD94GMcBuceILZ1Xtyoy6D8=', 'BKEu3tqd/WiWcvjGf+4xY23NjojQHUkBm9kLM+sz22k=', 'J+iNjBXzfc7kTx5UJaUd7L0TbOUJGmdn5J7JVEzNEBo=', 'L+7Re4QoXtm4pcjF6VpB9m4JZhmncDIjF2xB7kM95NE=', 'HtfMdu30XHxAQkFCD3Kc85TllCkRMSoNaXK4vVOv8rg=', 'FXQumbm/oyMVf/jFhvVmDqxng0dhRM3K3yh0vkVGaxo=', 'GqwoU4f2XoLIlfxoh930BXcQdFTG7AMXKE8DPyfQx4U=', 'JYUcPIRdR5D53a29tgVzV4MuLnpJd19x7HWpZVTWfHc=', 'FaWCFWXMLsLOeEV9sZft81O367osVSM3DdzMPZ8Uamc=', 'JBHVekgTuZgO+n4xodtZZtz2TzYEQndQLxVIXyjHFyc=', 'AC5vjWUgzUcT4zW4wLbS5kfpqY4S9M0lWIKLXvbLTJs=', 'L/e8j0OAzemX2gC2FrD80a+PDpHi/h7XOYg0YJ4DFdI=', 'ALmDG5SFJVle4CckRxvNGC6VIfa3u2jx6Tvk/rsNPL4=', 'Ci9TdouOv2qGkTsOV8BOARykCGSKR0OofXetvwycNRI=', 'ACSBVhQv0Dc6R5+R/yOelg9Zn/fpS+abfyopAwXhGY0=', 'Fx1WILh7+xMoz4wCqz8MmjlxlqpqVCwjUOtRKisrzak=', 'FwpPVVNvfclwCHx8ENb612DJUhct1U3ZnRBF5Ow0qAg=', 'KaujP3mf5mwu8xNK6gQzbsw344wc0hG6SC7KF+Lb+uE=', 'HpvBeaT911j90bsZRQiNR+cNEUoD9qDotbplA2nmSXM=', 'HdJpeZtmD61Y9/SJLfsLWv6q2GmpxLRPnJ4cQ72vjwk=', 'Is28i3ARetFAEYHQLhVFnnzNQm/oacfJXR3Syw8krzg=', 'DvBC5FR3HFM6n1elXFA/zv0xUPUu2Up81bqTucfazv0=', 'EWCeBq1sj+Lyh/MDYDfohRMY6LCKA1mgOzBP/KYugoQ=', 'EWbZ5VRhbbqedT7qQnwXt/7NWMB23+QnCLCPW3g6qa8=', 'LeUpiUMahZWTQTAmNUQT2xd/v0zSrAtW+FWoiDV+5GY=', 'MAbrT/x6hYGabaSS86isHfUa7lsXuOiddL8Bz19x6a0=', 'KvQfu2G6ioD9z2//nj9vQimT/o8KRjn5YjRMgiUUUIY=', 'EZ5oTeR2FV/lprQajryF24cYqyeInoXngbIUus5IJ8M=', 'GDW3huLokl4Yi+pZrjY1N7USSMI4KPBHz/eEuXs/2AA=', 'KCAaNMWU36NNeUmWxkM6INFSusKnkFySbEDihasy7rY=', 'CD79eifRdRCU6A/vr3iwAIZMgutXEYdySnYfiMIsxOc=', 'C2+Io1dxmVJhWOYc7qJ76BHBbfd3TdhRngeVZPYf0Ts=', 'Dsho5tFeUdlkT2bh1kcalFiVEcoA0p4QFDkObuQlT1s=', 'KvM+P4ZncScawMmz7S4RQuzT50uTnNQNANk3q4TJhZE=', 'C1ICEfkEtefQm12WHGrOdzRWjFR91oWLNkzl5HlR8Xg=', 'Cy1yLQkZoarY21jxAGKpLqDFasQnDoIsyiKGIBiKHUA=', 'H3kNTX+M8JTZgM6zfCRT6Ve1SpmRyji74AYdHtblYtQ=', 'AXHrld+/fR6uqXzThfeAFQiFwWI1oqao2pLOsB5QQjM=', 'DC0OO1/VdUkym/aIXaZrm3kLQN79LIZQdiMFOBsWiHM=', 'EWL7KGicJxVOWoIotOcrN3y8r6WJ4oPDXTgDBUQHoY0=', 'LxRZtl3uRBtkrThqkegxDygsWpKonhmSFiPvgklxG8A=', 'Hm/zIWtojD2ZbXQ2fVzUwbxInUZ1TrcSwkP3DRtTz7s=', 'AcqL5zgyuNBoFIfSfRV4AtdBpvNs3CoFdogfkyZHiHU=', 'H3c1cG/+n8WG+XbVvfIj3GgChggLEM6gC5td4xX5ZQ4=', 'JSK2D06jMHZAoMLc4EH7qSGsEKPV8JbvR0XKg4KF8Bk=', 'I/C+4AGxAp1SVQdd3JV/gzQYytT1K2w/jOFsI1VyV1s=', 'K8Gui43buB/KrC1EVV7VaF0UJjPp35BfZtlAEJMILVk=', 'D5QGuCllZKNzBFB7jbo+0WI3EnOgex/JgBH81q1yIF8=', 'I2Co6wzH3vpntymY3pBxThfnWxdKUu5KyxJsjNmV8Kg=', 'FYcaXN3q2XaATIA8uu8lXrSBWl6W34sAbcu8J2f4iUg=', 'GTpWdmmY7p4KhlLdLzsdoDYvT1T3I3lUT5V8ze77Qg8=', 'KjlKQ5NPhpgvm+Vv9PqxcDsuY8itM0g05DCYBed3rg8=', 'GFmVTP64aV8+i2NdyzRRkoks0RIjRDuntBZuiHbA0UI=', 'BOEYF2MFDlgBNETby5nxkCsRvCXZC73KQI04GfT+0ys=', 'D9slPe6Dhp1AwzXqZN6MW7EOuC2wi16LH15VUr/QXyM=', 'BYy+ippQJ72qTvtiOt6tYnXwhobxwImEqdfFuum08cA=', 'E4Ltzplx4YZJfq2xrrH1KyO0uDvvAjqw0VIotMzspZo=', 'A0ZJkPBFxu4IGcpR/RGwvn9huOuZ8Ut34eZjRgHZ6LU=', 'I/e/yHINwpb/8ztB+Y/4PG/KtGBdsutaqlvBN663Clg=', 'ClmhWOPuwhF+bpTn8OnezxjD/9XhUxqSGWNhWLuvYvI=', 'BuxUyAOBwFK1i/I7MS/9POLE66BlQgr49MI+0Adf0Hs=', 'EYhy3IMuDrVHa1ZkjoZ+yLCTQPenvLG0li8P+e0fnQE=', 'E9afoSfYNBZa1cfLp61Z7VLgsPDkLX/qleGQa1IJIbE=', 'FpoXf2PqaBJwscaHenPSG94UOUL7cdxV/YpJ8Z8Qx3s=', 'BO9RWRxurZfvQvKHrc5A2Tq+sDK5IvZv+36aWnRQVE0=', 'JW4XWh3AeTkOzXynA/suOxnsYYBdTwPO1fRe5t0Paew=', 'MBAtKGNqvV/l8q9BL/YAT3XMNg0yBd0toAKBPT4s7rI=', 'EJmOQt/NO78cBxS8c+sb9ARDo/qZvvSjH9Mb4YL8x5I=', 'GT7djp/PPXYl+n0ktZih2J8zYur01YLv7K12+HnjaGA=', 'GBaK/TTy2RXQNozoC3szR9HHpWHOYRQl8mZNeqUfC10=', 'KTg8AevTtqsMAXZW6+ZYtqMo7He8M2JuKeLpWzPqYRE=', 'EGRtLyYD3jmh9K5ed3GmSnAttuhvt2q2AL9XP5AQxxE=', 'C+teB9GycUX1dfE5WlW/Ey+QwltA2ns4ZNAkLcsRF/s=', 'FtaFJSB4wTPcDT7K1itciDD5W7LlS1mr3/vwGNlvozY=', 'Cmq9HYM5OPM8dBVOBAS0tApVW7vsId36/Wct1iBH8Bo=', 'GmefXTbre1yOoSpMLe3I/rEt/+7EUDFycKbxmzTPGGA=', 'CYD7IzvUVsI5dNUODr/eRyakI+raTo9v+8dZLj8bk9Y=', 'FhtCIy5huEy/GBCvk6OPwM7OPVYoySggA+ustcMSxys=', 'CtoQqQx/BSCVD31Hpg1eakk/CXh/FWTl0JID20feGgs=', 'GnMNNyMQuoIyA0WimsQjjtPweoorThIbtQ3bmvQH9FE=', 'LIEg8mjvBU+BcGTDad2n6pCDd/6rpcTf+9oQ71joxVY=', 'HHyIJPdYdT+lfAB4nGhCF7kw6VMTvLc+bnuGSaSWj3A=', 'LNntMfX4aRyOOeQHenT6oPQArYtJHrP3tHsn+j/Rz3c=', 'I/9PnUaBNFfPYNkvV2GDmaXgIqwyHKVQhUriORiiLuo=', 'CZRaXRR6T2bO7OZAXd3Z0K9aLFEDUpQH3/HqWPGAQm0=', 'GI2cUoAl1MK2dmDGt3G5D3x9puqinT8mim3SI+xvxjA=', 'MFDjeZZZa3+B9oMRQx2HNNun2SbTYzWV4MDY3fTw9H8=', 'Fa8RaTloMKkWAMqBAsNcQmzq5UYeP5XYnYKVGNMK/Xg=', 'HabQmIVDLqmgbZ83+HPZhdrpM+NRRmspBChNozINisw=', 'J5bqkNJpryn1+KzzOSESTk5PrT2+ZYlF5UbuQR3aqcs=', 'IC190doPa0sDJcizMHdC8B4VYS7I6TBKfLAxngHTLWA=', 'CW1nkNBbt1kVapUromPWcqLX+ceI9Mgxop2s5MD4vl8=', 'BU76H2Ww/OKDgIllJ12He0ONojzlsT4ZY3mMsUR9JaQ=', 'GxYvg9kX6T7bMwjCmALeudiqaQETsuFIZMz24Y5BZfE=', 'IeUkHhJWTdb9nxzdKg3jnu3+/BRmzFaOxc63RaBQbtw=', 'HPtWYujPWskiaoDuF7Nqvstzq1+H4WGSe0NJ4Q5L3wg=', 'DyEXfjAqdxu65tjR7LNztiyZrzRiIKwBKcU/Zm6yQQA=', 'FnFSI3RgaZKv+w3X9xsSvsQjau3mKQVGvO9+H1FcIyA=', 'D6PsW5SIJZwutM8kUBv62b4uyeQsXMjM1BnSppLK2HA=', 'GTwOBOC9KYNXyyZsFQYIDtNu3OhcZIzAhejFexq1S7o=', 'ECrfjvdHNaJ+kSgwbcvDyZ9vcpHNQGV4zhTqKtq6aPg=', 'D+CveFjkmFnipU1vGtlFsTFqokv73SOuQKbQy3DD6rE=', 'IW9nF7vH3tsIU2oiIIQ/Ti2l8dqp69796KXqc0R5jSI=', 'HaVcyQDw0h9KPmlDkZGKGzwjsqx3PGs++I4uQigyUWE='],
  M: [['EJt/QRug5MmytwyvXDansZS+fBGtJDeL/ttoWSuoEYs=', 'Fu1B4Tu5wMZq4RlCT928vJMU3J/b3upV1sZFQ9xJA+A=', 'K5C7oA/KBYn2F+fcv+guDfcGq2QM6yR7eRqTt042c20='], ['KWnyfu0xpIC5w2x2Q3nbyizI/dFBXD3e1ilAvN4L13E=', 'LiQZ+ewC7DlMmHHIMpY9wbiddDyMe5ZAKbIxFoex/iM=', 'EBBx8AMjebaXMVh2aQ8FPRSNThCfX7BlyKrMVaD4m/o='], ['FDAh7GhqPzMNX55lRjgGXObNeeKMWzdTMmJE7mWhsac=', 'F2zAKWla0CWCpw7/CKb9mdBX4S5Y59e2sWzfq8juKRE=', 'GaP8ClZwK/QXun/uOAJZP6ZERwMHBD93cyec1x0l1eA=']]
};
_2$2.default = _default$4;

Object.defineProperty(poseidon2$1$1, "__esModule", {
  value: true
});
var poseidon2_2$2 = poseidon2$1$1.poseidon2 = poseidon2$4;
var _poseidon$4 = _interopRequireDefault$4(poseidon_1$2);
var _unstringify$4 = _interopRequireDefault$4(unstringify$2);
var _$4 = _interopRequireDefault$4(_2$2);
function _interopRequireDefault$4(obj) { return obj && obj.__esModule ? obj : { default: obj }; }
const c$4 = (0, _unstringify$4.default)(_$4.default);
function poseidon2$4(inputs) {
  return (0, _poseidon$4.default)(inputs, c$4);
}

/**
 * Creates a keccak256 hash of a message compatible with the SNARK scalar modulus.
 * @param message The message to be hashed.
 * @returns The message digest.
 */
function hash$1(message) {
    message = BigNumber.from(message).toTwos(256).toHexString();
    message = zeroPad(message, 32);
    return BigInt(keccak256(message)) >> BigInt(8);
}

var Group = /** @class */ (function () {
    /**
     * Initializes the group with the group id and the tree depth.
     * @param id Group identifier.
     * @param treeDepth Tree depth.
     * @param members List of group members.
     */
    function Group(id, treeDepth, members) {
        if (treeDepth === void 0) { treeDepth = 20; }
        if (members === void 0) { members = []; }
        if (treeDepth < 16 || treeDepth > 32) {
            throw new Error("The tree depth must be between 16 and 32");
        }
        this._id = id;
        this.merkleTree = new IncrementalMerkleTree(poseidon2_2$2, treeDepth, hash$1(id), 2, members.map(BigInt));
    }
    Object.defineProperty(Group.prototype, "id", {
        /**
         * Returns the id of the group.
         * @returns Group id.
         */
        get: function () {
            return this._id;
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(Group.prototype, "root", {
        /**
         * Returns the root hash of the tree.
         * @returns Root hash.
         */
        get: function () {
            return this.merkleTree.root;
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(Group.prototype, "depth", {
        /**
         * Returns the depth of the tree.
         * @returns Tree depth.
         */
        get: function () {
            return this.merkleTree.depth;
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(Group.prototype, "zeroValue", {
        /**
         * Returns the zero value of the tree.
         * @returns Tree zero value.
         */
        get: function () {
            return this.merkleTree.zeroes[0];
        },
        enumerable: false,
        configurable: true
    });
    Object.defineProperty(Group.prototype, "members", {
        /**
         * Returns the members (i.e. identity commitments) of the group.
         * @returns List of members.
         */
        get: function () {
            return this.merkleTree.leaves;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the index of a member. If the member does not exist it returns -1.
     * @param member Group member.
     * @returns Index of the member.
     */
    Group.prototype.indexOf = function (member) {
        return this.merkleTree.indexOf(member);
    };
    /**
     * Adds a new member to the group.
     * @param member New member.
     */
    Group.prototype.addMember = function (member) {
        this.merkleTree.insert(BigInt(member));
    };
    /**
     * Adds new members to the group.
     * @param members New members.
     * @deprecated Use the new class parameter to add a list of members.
     */
    Group.prototype.addMembers = function (members) {
        for (var _i = 0, members_1 = members; _i < members_1.length; _i++) {
            var member = members_1[_i];
            this.addMember(member);
        }
    };
    /**
     * Updates a member in the group.
     * @param index Index of the member to be updated.
     * @param member New member value.
     */
    Group.prototype.updateMember = function (index, member) {
        this.merkleTree.update(index, member);
    };
    /**
     * Removes a member from the group.
     * @param index Index of the member to be removed.
     */
    Group.prototype.removeMember = function (index) {
        this.merkleTree.delete(index);
    };
    /**
     * Creates a proof of membership.
     * @param index Index of the proof's member.
     * @returns Proof object.
     */
    Group.prototype.generateMerkleProof = function (index) {
        var merkleProof = this.merkleTree.createProof(index);
        merkleProof.siblings = merkleProof.siblings.map(function (s) { return s[0]; });
        return merkleProof;
    };
    return Group;
}());

var poseidon1$3 = {};

const F$1 = BigInt('21888242871839275222246405745257275088548364400416034343698204186575808495617');

// Parameters are generated by a reference script https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/generate_parameters_grain.sage
// Used like so: sage generate_parameters_grain.sage 1 0 254 2 8 56 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

// Using recommended parameters from whitepaper https://eprint.iacr.org/2019/458.pdf (table 2, table 8)
// Generated by https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/calc_round_numbers.py
// And rounded up to nearest integer that divides by t
const N_ROUNDS_F$1 = 8;
const N_ROUNDS_P$1 = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
const pow5$1 = v => {
  let o = v * v;
  return v * o * o % F$1;
};
function mix$1(state, M) {
  const out = [];
  for (let x = 0; x < state.length; x++) {
    let o = 0n;
    for (let y = 0; y < state.length; y++) {
      o = o + M[x][y] * state[y];
    }
    out.push(o % F$1);
  }
  return out;
}
function poseidon$1(_inputs, opt) {
  const inputs = _inputs.map(i => BigInt(i));
  if (inputs.length <= 0) {
    throw new Error('poseidon-lite: Not enough inputs');
  }
  if (inputs.length > N_ROUNDS_P$1.length) {
    throw new Error('poseidon-lite: Too many inputs');
  }
  const t = inputs.length + 1;
  const nRoundsF = N_ROUNDS_F$1;
  const nRoundsP = N_ROUNDS_P$1[t - 2];
  const {
    C,
    M
  } = opt;
  if (M.length !== t) {
    throw new Error(`poseidon-lite: Incorrect M length, expected ${t} got ${M.length}`);
  }
  let state = [0n, ...inputs];
  for (let x = 0; x < nRoundsF + nRoundsP; x++) {
    for (let y = 0; y < state.length; y++) {
      state[y] = state[y] + C[x * t + y];
      if (x < nRoundsF / 2 || x >= nRoundsF / 2 + nRoundsP) state[y] = pow5$1(state[y]);else if (y === 0) state[y] = pow5$1(state[y]);
    }
    state = mix$1(state, M);
  }
  return state[0];
}
var poseidon_1$1 = poseidon$1;

var unstringify$1 = {};

Object.defineProperty(unstringify$1, "__esModule", {
  value: true
});
unstringify$1.default = unstringifyBigInts$1;
function unstringifyBigInts$1(o) {
  if (Array.isArray(o)) {
    return o.map(unstringifyBigInts$1);
  } else if (typeof o == 'object') {
    const res = {};
    for (const [key, val] of Object.entries(o)) {
      res[key] = unstringifyBigInts$1(val);
    }
    return res;
  }
  // base64 decode
  const byteArray = Uint8Array.from(atob(o), c => c.charCodeAt(0));
  const hex = [...byteArray].map(x => x.toString(16).padStart(2, '0')).join('');
  return BigInt(`0x${hex}`);
}

var _1$1 = {};

Object.defineProperty(_1$1, "__esModule", {
  value: true
});
_1$1.default = void 0;
var _default$3 = {
  C: ['CcRunsaOm9T+H6q6KUy6OKcaoXdTTN0bbH3A29Cr16c=', 'DANWUwiW7sQql+2TfzE1z8UUKzrkBbg0PB2D/6YEy4E=', 'Hiih2TVpitEULlEYK7VM9KAOpaq9Ymi9MX6pd8wVSjA=', 'J68tgxqdJ0gICWXbMOKY5A5XV8PgCNuWTPnisSuRJR8=', 'Hm8RzmD8j1E6ajz+Fq4XWkEpFGLyFM0Iear0NUW3TgM=', 'Kmc4TTu9XkOFQYGctoHwvgRGLtFMNhPY9xkgYmjRQtM=', 'C2b981YJOmEWCfjhL7/s8LmF44HwJRiJNkCPXVyfRdA=', 'AS7j7B541HCDDGEJPCreNwsmyDzFzr7t2qaFLb2wniE=', 'AlK6X2dgv739iPZ/gXXj/WzRxDGwmba7LRCOe0Rbsbk=', 'F5R0zOyl/2dsa+w871QpY1Q5Gok1/3HW71rqrXypMvE=', 'LCQmE3mlG/qSKP9KUD/U7Zwfl0omSWmzfholibvtK5E=', 'HMHXtiaS5j6sLyiL0GlbQ8L2P1AB/A/FU+ZsBVGAGwU=', 'JVBZMBqtqYuy7VX4UpeelgB4Tb8X+6zQXZ7/X9nJG1Y=', 'KEN746wcsuR54fXA7M0ys66iQjSXCoGTsRwpzn5Z79k=', 'KCFqRC8uH3EcpPprU3ZusRhUjaj7T3jUM4diw39fIEM=', 'LB9HzRf6Wt8fOfTnBW3QP+7h784DCUWBEx8jdzI0gsk=', 'B6utArel68SGMrzJNWzrfdna/KJ2Y4pjZGuFZqYhr8k=', 'AjAmRgH/3yknWzP/qrUd/pQp+QiAppzRN9oMTRX5bDw=', 'G8lzBU5R2QWg8WhlZJfKQKhkQUVX7iiecX5dZomaoKk=', 'Lhwi+WRDUAggbDFX6GNB7dJJr/XC2EIfKmsiKI8KZ/w=', 'EiTzjfZ8U3gSHB1fRhu8UJ6OoVmORsn3pwRSvCu6hrg=', 'AuTmnYulnlGSgLS9ntAGj9e/6M2d/toZadKYkYbN4g4=', 'Hx7Mw0qroBN/XfgfwE/z7k8Z7jZOZT8HbUfpc12YAY4=', 'FnKtPXCaNTl0JmwwOamnMRQkRIAyzRgZ6suKTUKE9YI=', 'KD4/3CxuQgxW9Er1GStK6c2mlh8oTSSZHS7WAt+Mj8c=', 'HCo9EgxVDs/Q2wlXFw+gE2g3Ufj9/1nWYU+9af85S8w=', 'IW+Eh3qsYXL3iXpzI0Vu/hQ6mkN3PqbylstrgXdlP70=', 'LA0nK+zyp1dkun6OPijRK86qR+phylmkEaH1FVL5R4g=', 'FuNCmYZcDihITuenTEVOnxcKVICr4FCPy0psPYlUb0M=', 'F1zrpZnpb1s3WiMqb7nMcXcgR3ZYAikPSM2Tl1VIj8U=', 'DHWURA3EjBb+rZ4XWLAoBmqkEL+8NU9U2MX/u0Sh7jI=', 'GjwpvDnyG7XEZtt9frb9j3YOIAE8z5EskkeYgtkZ/Y0=', 'DM/dkG80JuXAmG6gSbJTQAhV00kHT1pmlcjuq80i5o8=', 'FPa8gdnxhvYr20dc5slBGGanqKP9Bls84OaZtn3Z55Y=', 'CWK4J4n7PRKXAspwsvbFqswJmBDJxJXIiO3rc4a5cFI=', 'GogK9wdNGLO/IMed4lEnvBMoSrAe8CV1r+8Mj2oxqG0=', 'EMuhhBmmozLNXnfwIRwVSyCvKST8IP8/TDASu3rpMRs=', 'BX5iqaj4mz69x2umOp6sqPontzGcrjQGdWooSfMC8Q0=', 'KHyXHekdwKvUSt9ThLSYjLlhMDu/Zc/1r6BBO0QoDO4=', 'Id8ziK8Wh7uzvKnaDMqQjx5WK8RtSrpOb395YOMGiR0=', 'G+XIh9JbznA+JcyXTQk0zXid+PcLSY/YPv+LVg4WgrM=', 'Jo2jb3blaPtoEXF1zqLNDdLLXUL9pazqSNWcJwag1cE=', 'DherCR9urlDGCb6vVRDs7MXYu3QTXr0FvQZGDMJqXtY=', 'BNcn5yj/oKZ67lNasHSkMJHvYtjPg9JwBA9cqh9ir0A=', 'DdvXv5wpNBWBtUl2K8Ai7TNwKsEPG/2GKxVBfX45ym4=', 'J5DrM1FiF1J2gWLoKYnGwjT1sNHTr5tYiinEnIeJZUs=', 'HkV8YBpjtz5EcZUBk9ilcDlfPZq4sv0JhLdkIGFC+ek=', 'Ia5kMB3KliVjjWqyu+cTX/qQ7NDEP/kfxMaG/EbgkbA=', 'A3n2PIzjRo1NopMWb0lJKIVL6eNDLglVWFhTTu2NNQs=', 'AC1WQgNZ0CZqdEoICAngVMoOSSGkZoasjJ9YoyTDUEk=', 'EjFY5ZZbXZsdaLPNMuELvtqNYkWeIfQJD8LFr5Y1FaY=', 'C+KfxAhHqUFmHRS79svgQg+7K29Sg21OYMgOtJytnsE=', 'Gslpkd7CuwVXcWFCAVpFPDbbnYWcrV+aIzgC8k/fTBo=', 'FZZEP3Y9vMJfSWT8YdI7Pl4SyfqX8YqSUcozVbywYn4=', 'EuC802VL36drKGHU7Drq4PGFfZ8X5xWu1tBJ6uO6MhI=', 'D8krTxu+qCuepz1K+a8qUM6rrH83FUsZBObHbHz5ZLo=', 'H5wLFhBEZELW8uWSqAE/QLFPfHciI29PnH6WUjOHJ2I=', 'Dr10JErnJnX4zeBhV6eC9AUNkU2ji0wFjRWfZD279NM=', 'LLfw7Tnhbp9pqfr9SrlRwDsGcelzRu45eoOYOdzPxtE=', 'Gp1uLs/wIsxWBUQ+5BurIM52HQUUzlJmkMcrynNS2b8=', 'KhFUOWB/M1peqDw7xEqTMdDBMyapp7owh9oYLWSOxy8=', 'I/m2UptdBA0VuPp67j40EOc4tWMFzUTylTXBFcWkwGA=', 'BYcsFtsPcqIkmsa6SEu5w6POl8FtWLaLJg65OfDm6Kc=', 'EwC97gi7eCTKIPuAEYB19AIZthUdVbXFK2JKfN7d9qc=', 'Gbm2PS8QjhfmOBeGOo9sKI160pkW2YyxBy5Oe31Ss3Y=', 'AVvuE1fjwBW1vaI3ZoUi9hPRyIcmtexCJKIBKEgbT38=', 'KVNzbpS7a58blwek8WFeTv4eHOS6shjL6pLHhbEo/9E=', 'CwaTU7oJFhiGL4BhgMA4X4UbmNNytF9UTOcmbtZgjfw=', 'ME901GHMwTEV5OC8+5OBflWut+uTBrZOT1iKyX2B9Ck=', 'FbvxRs6bygnooz9ed9/k9arSoWSkYXpMuO5UFc3pE/w=', 'CrTf4MJ0LN5EkBAxSHlk7ZuPS4UEBcEMqf8jhZVyyMY=', 'DjLbMgoETjGX9F92SaGWde9e7f6lRt6pJR3jn5Y5d5o=', 'ChdWqh83jKSydjWni2iI5meXczqCd0iWoweO+lFtoBY=', 'BExKM7EPaTRH/RcXf5Uu+JXmHTKPhe+pQlTWoqJdk+8=', 'LtNhG3JbinC+ZVtTf2b3AP4IedeaSWiR03sHtUZsS4s=', 'H5uk6Lq3zkLI7MPXIqouDq3965z900e12DOepxIIWKo=', 'GyMwQwUujCiPfukHqE5RiqOOgqxFAgZtt0BW+GXF09o=', 'JDHhzBZLuNB0Axq3K9VbTJAgU7/A8U2wyi+XsCCHWVQ=', 'CC+TTJH1qsMwzWlToKfbRaE+MiCXWDMZp5Hyc5ZYAf0=', 'K5oKIj51OLCjS+B0MVVCo8dyReKufL6Zmta7kwxImXw=', 'DhzZHt0s+izOuFSDuIepvoFkFj51qKAOsLWJzHAhTn0=', 'Lh6sDyv9/WPJUfYUd+NpiZl3TxmFTQD1iNMkYBzr4vk=', 'DL+pXzf7dAYMdhWOdp1tFXNFeE2O/bM8I9dIEVtQC4M=', 'CPBbO+kj7UTWWtSdimHppnbZkeOndRPZmAwjLfpKT4Q=', 'InGeKgcLzQhSv44hmE0EQ+coSSXcB1ijJaLdUQwEfvY=', 'BB9Zap7hyyvAYPf8w6GrTHvb8DYRmYLA9B9isvJoMMA=', 'Iz/TXeG+UgqHYo6wb2sdTAIb4cLQ3EZKGfzdCYaxD4k=', 'BSS0bRqoel5DJeCkI+vIENMeB4qhtHB+78tFPGHJwmc=', 'LDT0JMgeVxbOR/ysiUuFgkInu5VLDzGZzESGI3xRUhE=', 'C18qS2M4eBkgfv/CtVQfty3SAltUV8yX8zAQMn3kkV4=', 'IiB4VggszFTFty/kOdLP1sF0NdL1evbOrvrEH+BcZZ8=', 'JNV6i/XaY/5OJBWbf4lQtc37IQGUyvefJ4VASM4sgXE=', 'Cvqxgf3V4Fg7Nx11vWk/mDdK1wl7sBqFc5Gbsjt5OW4=', 'LbqbEI8gh3KZilLvrHy9VnbABXGUwWwL8WKQ1isRKO4=', 'JjSbZu24sW9W+IHHiPU/g8u4PeC9WSslWv8T5rzkILM=', 'Ja984OXhA1doXpX5Izl1OtgaVtKOzBk7I1KIo+bxN9s=', 'JbTOe9IpQ5DAlNalXt1ouXDu16roiyv/H3wBh/41AR8=', 'IsVD8Q9siew4flPxkIqI5d6c7yjr3zCxjLnVTB4CtjE=', 'Ajb5PneJxHJPx5CKnxkeHkJekGqRnXo032aOdIgvh6k=', 'KTULQBFmygEOfSfjfQXamWUr2uEU6wFlnLSXr5gMS1I=', 'Du14fWWCDT9r0xu6tUf3WmXtt12ETruJ7hJgkWZSNj8=', 'B8wRcPE7RvIDanU/Ugsykf3NDpm9lCl9GQb2VvTeb60=', 'Irk5IzsdcgX0m89hOj0wsZCHhtf59dEMIFlDVonorOo=', 'AUUXYqCquByKrR3IvDPocHQPCDpaqFQ4rdZQrOYK5aY=', 'I1BrtdhyfURh+r8QJdRtH+MuqmHex9pX5wT+wIkvzok=', 'LkhMROg4rqC6wGrj9xvdCSo3CVMeHv6pf4vWiQc1VSI=', 'D0vH0H66/WQ3nnjFC9LkK69KWUVFztwlRUGNomg1tUw=', 'H008j2WD6eX6dmN4Yvqu6FFYI4hyXfRg5iCZbVDY504=', 'CTUU4McHEfgmYNB74OSpiPrgKrx7aB2RU+uby0j+c4k=', 'GtqwyOKzutNGaZorXzvANkPug+zkcijySljgo0fhU9g=', 'FnKxcmBX2Z3RRwnrtHRkGjeMG5S4ByusGiLb756A2tI=', 'Hf1T1Fdq8uOPRPU/3KtGjMXY4vrgrMTuMNR7I5tHnBQ=', 'DGiIoQt1sPOnCjYmOjfhf+bXfWQPb8PevH8gd1MgXGA=', 'Gt25M6Zb53CSs0p+d9Ev6GEaYeAO5oSLhQkezKnR5Qg=', 'ANdUDc0mioRcEK4Y0d6TPPY4/1Ql8K//eTVijimdF5E=', 'FAwOQmh+nq0BsoJ6VmTKnCb+3eSs2Z2x0xaTnSC4LA4=', 'Lww6EV1DF9GRuom40T0YBsIKD5sk+MXtwJHirlZWWYQ=', 'DE7neP98FFUwBu0iDPnIEAigz/ZwsiuC2MU4odyVjGE=', 'FwTydm1G+Cw2k/AEQMzDYJQk7SbArMZiJ8PXSF3nTGk=', 'Ly0ZzD6l146noCwbUdJEq/B2nJ+FROQCObZv6QCcPPo=', 'GuA4U7dfyrpQU/ES4qjo3N1+5suc/tnH1sdmqAb8Zik=', 'CXGqv3lSQd9R0THQ+mGqXzVWkhstbwFOTkGobdrwVtU=', 'FAjDFuYBThqR1M9rbg3nPtpiT4OA3xyHX1wp97/i9kY=', 'Fmfz/i7b6FAkir5CtUMJO2yJ8fdz7yhTQWkfOYIu9b0=', 'E798XQ0sQ3akiwoDVXzfkVuBcYQJ5cEzQkxpV2UA/jc=', 'B2IKbfsLbOwwFq3z01M8JAJLlTR4VreXGbwLp0OmLCw=', 'FXTH7wxDVF82qMoIvb3YsHXSlZ4vMitzFnXePhmCtNA=', 'Jp5LW3oushr9VnlwpxfO7FvUGEVxwlT9wG4Dp/+DePA='],
  M: [['Bm9vhdb2ioXsEDRTUaI6Oq8H84r4yVKnvOynC9KvetU=', 'K51LQRDJrpl3guFQmx0P2yCnwCu9i+pzBUYrn4Elseg='], ['DMV827CFB9Yr9npEk8wmL7bAnVVwE//x9XP0MSIfj/k=', 'EnTmSaMu01WjGm7WlyThra3oV+hutcOhIbzRR5QyA8g=']]
};
_1$1.default = _default$3;

Object.defineProperty(poseidon1$3, "__esModule", {
  value: true
});
var poseidon1_2$1 = poseidon1$3.poseidon1 = poseidon1$2;
var _poseidon$3 = _interopRequireDefault$3(poseidon_1$1);
var _unstringify$3 = _interopRequireDefault$3(unstringify$1);
var _$3 = _interopRequireDefault$3(_1$1);
function _interopRequireDefault$3(obj) { return obj && obj.__esModule ? obj : { default: obj }; }
const c$3 = (0, _unstringify$3.default)(_$3.default);
function poseidon1$2(inputs) {
  return (0, _poseidon$3.default)(inputs, c$3);
}

var poseidon2$3 = {};

var _2$1 = {};

Object.defineProperty(_2$1, "__esModule", {
  value: true
});
_2$1.default = void 0;
var _default$2 = {
  C: ['DumlkrqalRjQWYbWVvQMIRTEmTwRuymTjSHUcwTNjm4=', 'APFEUjXyFIxZhlhxafwbzYh7CNTQCGjfVpb/9AlW6GQ=', 'CN/zSH6KyZ4fKaBY0PqAuTDHKHMLerNs6HnziQ7Pc/U=', 'Lye+aQ/a7kbDzij3UysTyFbDU0LIS9puIJZjEPrcAdA=', 'KyrhrPaLe40kFr6/PU9iNLdj/gS4BD7ki4MnvryhbPI=', 'AxnQYgcr737MperAb5fU1VlSwXWrawPq5ktEx9vxHPo=', 'KIE9yuuuqoKKN234evSmO8i3vyetScYpjvezh78oUm0=', 'JydnOyzLyQPxgb844cHUDSAzhlIAw1K8FQkord35y3g=', 'I07EXKJ3J8LnSr0rKhSUzW771D40BYfWuPueMeZcxjI=', 'FbUlNAMa4Y9/hiyyz3z3YKsQqBUKM3sczZn/boeX1Cg=', 'Dcj61tnks19e2aPRhrec444Oio0bWLEy1wHU7s9o0fY=', 'G82V/8IR+8pgD3BfrT+1Z+pOs3j2Lh/sl4BVGKR+TZw=', 'EFILCrchyt/p7/gbAW/DTcdto2wleJN4F8uXjQad5Vk=', 'H21IFJuOf32bJX2O1fu69CkySYB1/tCs6IqeuB9WJ/Y=', 'HZZV9lIwkBTSngDvNaIIm//43ByBbw3JyjS9tUYMhwU=', 'BN9aVv+VvK+wUfexzUOpm6cx/2fkcDIFj+PUGFaXzH0=', 'BnLZlfj/9kAVGz0pDO2vFIaQoQqMhCSn9uwoK25L6Cg=', 'CZlStBSIRFSyEgDX/6/dXwyancwG8nCOn8HYIJtcdbk=', 'BSy6IlXf0Ax8SDFDuo1GlEjkNYaptM2Rg/0OhDprn6Y=', 'C4ut7mkK246wvXRxK3mZr4LeVXByUa13Fgd8uTxGTdw=', 'EZsVkPEzB69aHuZRAgwHx0nBXWBoOoBQuWPQqOSyvdE=', 'AxULfNbV0XslKdNr4PZ7gyxKz8iE707lzhW+C/tKjQk=', 'LMYYLF4UVG488ZUfFzkSNVN077g9gImKvmnLMXyepWU=', 'AFAyVR5jeMRQz+EppASzdkIYyt7awU4rktLNcxEb8Pk=', 'IzI34yibqjS7FH6XLry5UWRpw5n8wGn7iPnaLMKCdrU=', 'Bcj09OvUpuPJgNMWdL++YyMDfyGzSuWk6AwtTCTWAoA=', 'CnsdsTBC05a6BdgYoxnyUlK8817zru2R7h8JslkPxls=', 'KnO3H5shDPWxQpZXLJ0y2/FW4rCG/0fcXfVCNlpATsA=', 'GsmwQXq8yaGTUQfp/8kdw+wY8sTb5/Ipdqdgu1xQxGA=', 'EsAzmuCDdII/q7B2cH70eSafPk1ssQQ0kBXuBG3JP8A=', 'C3R1sQKhZa1/WxjbTh5wT1KQCqMlO6rGgkZoLlbpoo4=', 'A3woSeGRyj7bHF5J9ui4kXyEPjeTZvLqMqs6qI1/hEg=', 'BaaBH4VW8BTpJnRmHiF+m9UgbFyToH3BRf2xdqcWNG8=', 'KaeV59mAKJRulHt11U6fBEB26Hp7KIO0e2de9fOL1m4=', 'IEOaDISzIutFo4V6/Bj1gm6Mc4LIoVhcUHvhmZgf0i8=', 'Lguo2U2ez0qU7CBQxzcf8btQ8neZqEttSipvKgmCyIc=', 'FD/RFc4I+yfKOOt8zoIrRReCLNIQkEjS5tDdzKF9ccg=', 'DGTL7LHHNLhXlo273PgTzfhhFlkyPby/yEMjYjvpyvE=', 'AoowWEfGg/ZG/KklwWP/WudPNI1iwrZw8UJs75QD2lM=', 'Lk71EP8Lb9pfqUCrTEOA8mpry2TYlCe4JNZ1W1254ww=', 'AIHJW8QzhOZj15JwyVbOO4kltPbQM7B4uWOE9QV5QA4=', 'LtXwyRy9l0kYfi+t5ofgXuJJGzScA5oLuoqfQCOguzg=', 'MFCZkfiNo1BLvzdO1ari8DRIoix2I0yMmQ8B8zpzUgY=', 'HD8g/VVAmlMiG3xNSaNWufChEZ+yBntBp1KQlEJOxq0=', 'ELTn86td8AMElRRFm24Y7sRrsiE+jhMeFwiHtH3cuWw=', 'KhmCl5w/9/Q93VQ9iRwqvd2A+ATAd9d1A5qjUC5Dre8=', 'HHTuZPFeHbb+3b6tVtbVXbpDHrw5bJr5XK0PExW9XJE=', 'B1M+yFC6f5jquTA8rOAbS55PLouCcIz6nC/kWgrhRqA=', 'IVdrQ45QBEmhUeTurxexVChcaPQtQsGAihGr83ZMB1A=', 'LxfAVZuP55YIrVyhk9YvELzoOEyBXwkGdD1pMINtSp4=', 'LUd+OGLQdwinnoqulGFwvJd1pCATGEdK5mWwsbficw4=', 'Fi9SQ5ZwZMOQ4JVXeYTyka+6ImbDj1q82Jvg9bJ0fqs=', 'K0yyM+3pukgmTs0siuUNGteoWWqH8p+Kd3enAJI5MxE=', 'LI+8st2Fc9wduvj0YihUd22y7s5thcTPQlTnw14DsHo=', 'HW80dyXkgWry/0U/DNVrGZ4bYen2Aemt5eiNuHCUnak=', 'IEsMOX9OvnHrwtiz31uRPfnmrAK2jTEyTNSa9cRWVSk=', 'DEy53DxP2BdPEUmzxjw8L57LgnzX3CVTT/j7dbx5xQI=', 'F0rWGhRIyJmiVBZHT0kwMB5cSUdSeeBjmmFt3EW8e1Q=', 'GpYXe89NjYn3Wd9OwvPN4uqqKMF3zA+hOpgW1Jo40u8=', 'Bm0EskMx1xzQ74BUvGDE/wUgLBJqIzwagkKs42C4owo=', 'KkxPxuwLDPUhlXgoccbdOzgcxl9y4CrVJwN6Yqob2AQ=', 'E6stE2zPN9RH6fLhSnztyV5yf4RG9tnX5Vr8ASGf1kk=', 'ESFVL8omBhYZ0k2EPcgnacGwT87Cb1UZTC4+hprMapo=', 'AO9lMyKxPWyIm8gXFcN9d6bNJn1ZXEqJCaVUbHyXz/E=', 'DiVIPkWmZSCLJh2Lp0BR5kAMd21lJZXZhFrKNdijl9M=', 'KfU23LnddoIkUmRlnhXYjjlaw9Td6S2MRkSNuXnuuok=', 'KlbvnyxT/rrf2jNXXb29iFoSTieAu+oXDkVrqs4Ppb4=', 'HINhx461z13s+3otF7XECfKuKZmkZ2Lo7kFiQKjLmvE=', 'FRr/XziyCg/ARzCJqvAga4Po5op2RQe/09CrS+dDGcU=', 'BMYYfkHtiB3BsjnIj3+dQ6n1L8jIts3R525HYVtR8QA=', 'E7N72A9NJ/sQ2EMx9vttU0uBxh7RV3ZEnoAbfdycKWc=', 'AaXFNic8LZ31eL+9MsF7eizjZkwqUgMskyHOscToqOQ=', 'KrNWGDTKc4Na0F9desuVC0qaLGZrlybagyI5Blt8OwI=', 'HU2OwpHnINsgD+bWhsDWE6yvavTpXTv2n37VFqWXtkY=', 'BBKU0sxITSKPV4T+eRn9K7klNRJAoEtxFRTJyAtlrx0=', 'FUrJjgFwjGEcT6cVmR8ASJj1eTnRJuOSBClx3ZDoH8Y=', 'CzOdisyn1Pg+7dhAk671EFCzaEyI+LCwRSRWO8bqTaQ=', 'CVXknmYQyUJUpPhM+6s0RZjw5x6v9Kfdge2VtQg5yC4=', 'BnRqYVbrpUQmueIiBvFavKmm9B5vU1xvNSVAHqBlRiY=', 'Dxj1oOzRQjxJbzggxUnCeDjleQ4r0KGWrJF8f/Mgd/s=', 'BPbuyhdR9zCKxZ7/W+smHku1Y1g+3nvJKnOCI9b3bhM=', 'K1aXM2TExPXBo+xNo83OA4gR6xFvs+RbwXaNJvwLN1g=', 'Ejdp3UnVsFTc12uJgEsby44TkrOFcWpdg/62XUN/Ke8=', 'IUe0JPxIyAqI7lK5EWmqzqmJ9kRkcRUJlCV7L7AcY+k=', 'D9wfWFSLhXAabFUF6jMqKWR+bzStQkPC6lStiXzr5U0=', 'Ejc6glH+oATfaKvPD3eG1Lzv8oxdu+DDlE9oXMCgsfI=', 'IeT06l81+FutfqUv90LJ6KZCdWtq9EID3YofNcGpADU=', 'FiQ5FtadLKPftHIiJNTEYrVzZkkvRekNioGTTxvDsUc=', 'HvvkbdeleLT2b5rbyItDeKvCFWbhoEU8oTpBWcrASsI=', 'B+pehTfPXdCIhgIOI6fzh9Ro1VJb5m+FO2csyWqIlpo=', 'BajE+ZaLiqO3tHijD5pbY2UPGadefOEcqf4WwLdsALw=', 'IPBXcSzCFlT7/lm9NF6NrD94GMcBuceILZ1Xtyoy6D8=', 'BKEu3tqd/WiWcvjGf+4xY23NjojQHUkBm9kLM+sz22k=', 'J+iNjBXzfc7kTx5UJaUd7L0TbOUJGmdn5J7JVEzNEBo=', 'L+7Re4QoXtm4pcjF6VpB9m4JZhmncDIjF2xB7kM95NE=', 'HtfMdu30XHxAQkFCD3Kc85TllCkRMSoNaXK4vVOv8rg=', 'FXQumbm/oyMVf/jFhvVmDqxng0dhRM3K3yh0vkVGaxo=', 'GqwoU4f2XoLIlfxoh930BXcQdFTG7AMXKE8DPyfQx4U=', 'JYUcPIRdR5D53a29tgVzV4MuLnpJd19x7HWpZVTWfHc=', 'FaWCFWXMLsLOeEV9sZft81O367osVSM3DdzMPZ8Uamc=', 'JBHVekgTuZgO+n4xodtZZtz2TzYEQndQLxVIXyjHFyc=', 'AC5vjWUgzUcT4zW4wLbS5kfpqY4S9M0lWIKLXvbLTJs=', 'L/e8j0OAzemX2gC2FrD80a+PDpHi/h7XOYg0YJ4DFdI=', 'ALmDG5SFJVle4CckRxvNGC6VIfa3u2jx6Tvk/rsNPL4=', 'Ci9TdouOv2qGkTsOV8BOARykCGSKR0OofXetvwycNRI=', 'ACSBVhQv0Dc6R5+R/yOelg9Zn/fpS+abfyopAwXhGY0=', 'Fx1WILh7+xMoz4wCqz8MmjlxlqpqVCwjUOtRKisrzak=', 'FwpPVVNvfclwCHx8ENb612DJUhct1U3ZnRBF5Ow0qAg=', 'KaujP3mf5mwu8xNK6gQzbsw344wc0hG6SC7KF+Lb+uE=', 'HpvBeaT911j90bsZRQiNR+cNEUoD9qDotbplA2nmSXM=', 'HdJpeZtmD61Y9/SJLfsLWv6q2GmpxLRPnJ4cQ72vjwk=', 'Is28i3ARetFAEYHQLhVFnnzNQm/oacfJXR3Syw8krzg=', 'DvBC5FR3HFM6n1elXFA/zv0xUPUu2Up81bqTucfazv0=', 'EWCeBq1sj+Lyh/MDYDfohRMY6LCKA1mgOzBP/KYugoQ=', 'EWbZ5VRhbbqedT7qQnwXt/7NWMB23+QnCLCPW3g6qa8=', 'LeUpiUMahZWTQTAmNUQT2xd/v0zSrAtW+FWoiDV+5GY=', 'MAbrT/x6hYGabaSS86isHfUa7lsXuOiddL8Bz19x6a0=', 'KvQfu2G6ioD9z2//nj9vQimT/o8KRjn5YjRMgiUUUIY=', 'EZ5oTeR2FV/lprQajryF24cYqyeInoXngbIUus5IJ8M=', 'GDW3huLokl4Yi+pZrjY1N7USSMI4KPBHz/eEuXs/2AA=', 'KCAaNMWU36NNeUmWxkM6INFSusKnkFySbEDihasy7rY=', 'CD79eifRdRCU6A/vr3iwAIZMgutXEYdySnYfiMIsxOc=', 'C2+Io1dxmVJhWOYc7qJ76BHBbfd3TdhRngeVZPYf0Ts=', 'Dsho5tFeUdlkT2bh1kcalFiVEcoA0p4QFDkObuQlT1s=', 'KvM+P4ZncScawMmz7S4RQuzT50uTnNQNANk3q4TJhZE=', 'C1ICEfkEtefQm12WHGrOdzRWjFR91oWLNkzl5HlR8Xg=', 'Cy1yLQkZoarY21jxAGKpLqDFasQnDoIsyiKGIBiKHUA=', 'H3kNTX+M8JTZgM6zfCRT6Ve1SpmRyji74AYdHtblYtQ=', 'AXHrld+/fR6uqXzThfeAFQiFwWI1oqao2pLOsB5QQjM=', 'DC0OO1/VdUkym/aIXaZrm3kLQN79LIZQdiMFOBsWiHM=', 'EWL7KGicJxVOWoIotOcrN3y8r6WJ4oPDXTgDBUQHoY0=', 'LxRZtl3uRBtkrThqkegxDygsWpKonhmSFiPvgklxG8A=', 'Hm/zIWtojD2ZbXQ2fVzUwbxInUZ1TrcSwkP3DRtTz7s=', 'AcqL5zgyuNBoFIfSfRV4AtdBpvNs3CoFdogfkyZHiHU=', 'H3c1cG/+n8WG+XbVvfIj3GgChggLEM6gC5td4xX5ZQ4=', 'JSK2D06jMHZAoMLc4EH7qSGsEKPV8JbvR0XKg4KF8Bk=', 'I/C+4AGxAp1SVQdd3JV/gzQYytT1K2w/jOFsI1VyV1s=', 'K8Gui43buB/KrC1EVV7VaF0UJjPp35BfZtlAEJMILVk=', 'D5QGuCllZKNzBFB7jbo+0WI3EnOgex/JgBH81q1yIF8=', 'I2Co6wzH3vpntymY3pBxThfnWxdKUu5KyxJsjNmV8Kg=', 'FYcaXN3q2XaATIA8uu8lXrSBWl6W34sAbcu8J2f4iUg=', 'GTpWdmmY7p4KhlLdLzsdoDYvT1T3I3lUT5V8ze77Qg8=', 'KjlKQ5NPhpgvm+Vv9PqxcDsuY8itM0g05DCYBed3rg8=', 'GFmVTP64aV8+i2NdyzRRkoks0RIjRDuntBZuiHbA0UI=', 'BOEYF2MFDlgBNETby5nxkCsRvCXZC73KQI04GfT+0ys=', 'D9slPe6Dhp1AwzXqZN6MW7EOuC2wi16LH15VUr/QXyM=', 'BYy+ippQJ72qTvtiOt6tYnXwhobxwImEqdfFuum08cA=', 'E4Ltzplx4YZJfq2xrrH1KyO0uDvvAjqw0VIotMzspZo=', 'A0ZJkPBFxu4IGcpR/RGwvn9huOuZ8Ut34eZjRgHZ6LU=', 'I/e/yHINwpb/8ztB+Y/4PG/KtGBdsutaqlvBN663Clg=', 'ClmhWOPuwhF+bpTn8OnezxjD/9XhUxqSGWNhWLuvYvI=', 'BuxUyAOBwFK1i/I7MS/9POLE66BlQgr49MI+0Adf0Hs=', 'EYhy3IMuDrVHa1ZkjoZ+yLCTQPenvLG0li8P+e0fnQE=', 'E9afoSfYNBZa1cfLp61Z7VLgsPDkLX/qleGQa1IJIbE=', 'FpoXf2PqaBJwscaHenPSG94UOUL7cdxV/YpJ8Z8Qx3s=', 'BO9RWRxurZfvQvKHrc5A2Tq+sDK5IvZv+36aWnRQVE0=', 'JW4XWh3AeTkOzXynA/suOxnsYYBdTwPO1fRe5t0Paew=', 'MBAtKGNqvV/l8q9BL/YAT3XMNg0yBd0toAKBPT4s7rI=', 'EJmOQt/NO78cBxS8c+sb9ARDo/qZvvSjH9Mb4YL8x5I=', 'GT7djp/PPXYl+n0ktZih2J8zYur01YLv7K12+HnjaGA=', 'GBaK/TTy2RXQNozoC3szR9HHpWHOYRQl8mZNeqUfC10=', 'KTg8AevTtqsMAXZW6+ZYtqMo7He8M2JuKeLpWzPqYRE=', 'EGRtLyYD3jmh9K5ed3GmSnAttuhvt2q2AL9XP5AQxxE=', 'C+teB9GycUX1dfE5WlW/Ey+QwltA2ns4ZNAkLcsRF/s=', 'FtaFJSB4wTPcDT7K1itciDD5W7LlS1mr3/vwGNlvozY=', 'Cmq9HYM5OPM8dBVOBAS0tApVW7vsId36/Wct1iBH8Bo=', 'GmefXTbre1yOoSpMLe3I/rEt/+7EUDFycKbxmzTPGGA=', 'CYD7IzvUVsI5dNUODr/eRyakI+raTo9v+8dZLj8bk9Y=', 'FhtCIy5huEy/GBCvk6OPwM7OPVYoySggA+ustcMSxys=', 'CtoQqQx/BSCVD31Hpg1eakk/CXh/FWTl0JID20feGgs=', 'GnMNNyMQuoIyA0WimsQjjtPweoorThIbtQ3bmvQH9FE=', 'LIEg8mjvBU+BcGTDad2n6pCDd/6rpcTf+9oQ71joxVY=', 'HHyIJPdYdT+lfAB4nGhCF7kw6VMTvLc+bnuGSaSWj3A=', 'LNntMfX4aRyOOeQHenT6oPQArYtJHrP3tHsn+j/Rz3c=', 'I/9PnUaBNFfPYNkvV2GDmaXgIqwyHKVQhUriORiiLuo=', 'CZRaXRR6T2bO7OZAXd3Z0K9aLFEDUpQH3/HqWPGAQm0=', 'GI2cUoAl1MK2dmDGt3G5D3x9puqinT8mim3SI+xvxjA=', 'MFDjeZZZa3+B9oMRQx2HNNun2SbTYzWV4MDY3fTw9H8=', 'Fa8RaTloMKkWAMqBAsNcQmzq5UYeP5XYnYKVGNMK/Xg=', 'HabQmIVDLqmgbZ83+HPZhdrpM+NRRmspBChNozINisw=', 'J5bqkNJpryn1+KzzOSESTk5PrT2+ZYlF5UbuQR3aqcs=', 'IC190doPa0sDJcizMHdC8B4VYS7I6TBKfLAxngHTLWA=', 'CW1nkNBbt1kVapUromPWcqLX+ceI9Mgxop2s5MD4vl8=', 'BU76H2Ww/OKDgIllJ12He0ONojzlsT4ZY3mMsUR9JaQ=', 'GxYvg9kX6T7bMwjCmALeudiqaQETsuFIZMz24Y5BZfE=', 'IeUkHhJWTdb9nxzdKg3jnu3+/BRmzFaOxc63RaBQbtw=', 'HPtWYujPWskiaoDuF7Nqvstzq1+H4WGSe0NJ4Q5L3wg=', 'DyEXfjAqdxu65tjR7LNztiyZrzRiIKwBKcU/Zm6yQQA=', 'FnFSI3RgaZKv+w3X9xsSvsQjau3mKQVGvO9+H1FcIyA=', 'D6PsW5SIJZwutM8kUBv62b4uyeQsXMjM1BnSppLK2HA=', 'GTwOBOC9KYNXyyZsFQYIDtNu3OhcZIzAhejFexq1S7o=', 'ECrfjvdHNaJ+kSgwbcvDyZ9vcpHNQGV4zhTqKtq6aPg=', 'D+CveFjkmFnipU1vGtlFsTFqokv73SOuQKbQy3DD6rE=', 'IW9nF7vH3tsIU2oiIIQ/Ti2l8dqp69796KXqc0R5jSI=', 'HaVcyQDw0h9KPmlDkZGKGzwjsqx3PGs++I4uQigyUWE='],
  M: [['EJt/QRug5MmytwyvXDansZS+fBGtJDeL/ttoWSuoEYs=', 'Fu1B4Tu5wMZq4RlCT928vJMU3J/b3upV1sZFQ9xJA+A=', 'K5C7oA/KBYn2F+fcv+guDfcGq2QM6yR7eRqTt042c20='], ['KWnyfu0xpIC5w2x2Q3nbyizI/dFBXD3e1ilAvN4L13E=', 'LiQZ+ewC7DlMmHHIMpY9wbiddDyMe5ZAKbIxFoex/iM=', 'EBBx8AMjebaXMVh2aQ8FPRSNThCfX7BlyKrMVaD4m/o='], ['FDAh7GhqPzMNX55lRjgGXObNeeKMWzdTMmJE7mWhsac=', 'F2zAKWla0CWCpw7/CKb9mdBX4S5Y59e2sWzfq8juKRE=', 'GaP8ClZwK/QXun/uOAJZP6ZERwMHBD93cyec1x0l1eA=']]
};
_2$1.default = _default$2;

Object.defineProperty(poseidon2$3, "__esModule", {
  value: true
});
var poseidon2_2$1 = poseidon2$3.poseidon2 = poseidon2$2;
var _poseidon$2 = _interopRequireDefault$2(poseidon_1$1);
var _unstringify$2 = _interopRequireDefault$2(unstringify$1);
var _$2 = _interopRequireDefault$2(_2$1);
function _interopRequireDefault$2(obj) { return obj && obj.__esModule ? obj : { default: obj }; }
const c$2 = (0, _unstringify$2.default)(_$2.default);
function poseidon2$2(inputs) {
  return (0, _poseidon$2.default)(inputs, c$2);
}

function getMessageHash(message) {
    return poseidon1_2$1([discreetlyInterfaces.str2BigInt(message)]);
}
function getRateCommitmentHash(identityCommitment, userMessageLimit) {
    return poseidon2_2$1([identityCommitment, userMessageLimit]);
}
const wasmPath = './rln/circuit.wasm';
const zkeyPath = './rln/final.zkey';
const prover = new rlnjs.RLNProver(wasmPath, zkeyPath);
async function genProof(room, message, identity, messageId = 0, messageLimit = 1) {
    console.log(room, message, identity);
    const RLN_IDENIFIER = BigInt(room.id);
    const userMessageLimit = BigInt(messageLimit);
    const messageHash = getMessageHash(message);
    const group = new Group(RLN_IDENIFIER, 20, room.membership?.identityCommitments);
    const rateCommitment = getRateCommitmentHash(identity.getCommitment(), userMessageLimit);
    const proofInputs = {
        rlnIdentifier: RLN_IDENIFIER,
        identitySecret: identity.getSecret(),
        userMessageLimit: userMessageLimit,
        messageId: BigInt(messageId),
        merkleProof: group.generateMerkleProof(group.indexOf(rateCommitment)),
        x: messageHash,
        epoch: BigInt(Date.now().toString())
    };
    //console.debug('PROOFINPUTS:', proofInputs);
    return prover.generateProof(proofInputs).then((proof) => {
        console.log('Proof generated!');
        const msg = {
            id: proof.snarkProof.publicSignals.nullifier.toString(),
            message: message,
            roomId: RLN_IDENIFIER,
            proof
        };
        return msg;
    });
}

var sha512 = {exports: {}};

/*
 * [js-sha512]{@link https://github.com/emn178/js-sha512}
 *
 * @version 0.8.0
 * @author Chen, Yi-Cyuan [emn178@gmail.com]
 * @copyright Chen, Yi-Cyuan 2014-2018
 * @license MIT
 */

(function (module) {
	/*jslint bitwise: true */
	(function () {

	  var INPUT_ERROR = 'input is invalid type';
	  var FINALIZE_ERROR = 'finalize already called';
	  var WINDOW = typeof window === 'object';
	  var root = WINDOW ? window : {};
	  if (root.JS_SHA512_NO_WINDOW) {
	    WINDOW = false;
	  }
	  var WEB_WORKER = !WINDOW && typeof self === 'object';
	  var NODE_JS = !root.JS_SHA512_NO_NODE_JS && typeof process === 'object' && process.versions && process.versions.node;
	  if (NODE_JS) {
	    root = commonjsGlobal;
	  } else if (WEB_WORKER) {
	    root = self;
	  }
	  var COMMON_JS = !root.JS_SHA512_NO_COMMON_JS && 'object' === 'object' && module.exports;
	  var ARRAY_BUFFER = !root.JS_SHA512_NO_ARRAY_BUFFER && typeof ArrayBuffer !== 'undefined';
	  var HEX_CHARS = '0123456789abcdef'.split('');
	  var EXTRA = [-2147483648, 8388608, 32768, 128];
	  var SHIFT = [24, 16, 8, 0];
	  var K = [
	    0x428A2F98, 0xD728AE22, 0x71374491, 0x23EF65CD,
	    0xB5C0FBCF, 0xEC4D3B2F, 0xE9B5DBA5, 0x8189DBBC,
	    0x3956C25B, 0xF348B538, 0x59F111F1, 0xB605D019,
	    0x923F82A4, 0xAF194F9B, 0xAB1C5ED5, 0xDA6D8118,
	    0xD807AA98, 0xA3030242, 0x12835B01, 0x45706FBE,
	    0x243185BE, 0x4EE4B28C, 0x550C7DC3, 0xD5FFB4E2,
	    0x72BE5D74, 0xF27B896F, 0x80DEB1FE, 0x3B1696B1,
	    0x9BDC06A7, 0x25C71235, 0xC19BF174, 0xCF692694,
	    0xE49B69C1, 0x9EF14AD2, 0xEFBE4786, 0x384F25E3,
	    0x0FC19DC6, 0x8B8CD5B5, 0x240CA1CC, 0x77AC9C65,
	    0x2DE92C6F, 0x592B0275, 0x4A7484AA, 0x6EA6E483,
	    0x5CB0A9DC, 0xBD41FBD4, 0x76F988DA, 0x831153B5,
	    0x983E5152, 0xEE66DFAB, 0xA831C66D, 0x2DB43210,
	    0xB00327C8, 0x98FB213F, 0xBF597FC7, 0xBEEF0EE4,
	    0xC6E00BF3, 0x3DA88FC2, 0xD5A79147, 0x930AA725,
	    0x06CA6351, 0xE003826F, 0x14292967, 0x0A0E6E70,
	    0x27B70A85, 0x46D22FFC, 0x2E1B2138, 0x5C26C926,
	    0x4D2C6DFC, 0x5AC42AED, 0x53380D13, 0x9D95B3DF,
	    0x650A7354, 0x8BAF63DE, 0x766A0ABB, 0x3C77B2A8,
	    0x81C2C92E, 0x47EDAEE6, 0x92722C85, 0x1482353B,
	    0xA2BFE8A1, 0x4CF10364, 0xA81A664B, 0xBC423001,
	    0xC24B8B70, 0xD0F89791, 0xC76C51A3, 0x0654BE30,
	    0xD192E819, 0xD6EF5218, 0xD6990624, 0x5565A910,
	    0xF40E3585, 0x5771202A, 0x106AA070, 0x32BBD1B8,
	    0x19A4C116, 0xB8D2D0C8, 0x1E376C08, 0x5141AB53,
	    0x2748774C, 0xDF8EEB99, 0x34B0BCB5, 0xE19B48A8,
	    0x391C0CB3, 0xC5C95A63, 0x4ED8AA4A, 0xE3418ACB,
	    0x5B9CCA4F, 0x7763E373, 0x682E6FF3, 0xD6B2B8A3,
	    0x748F82EE, 0x5DEFB2FC, 0x78A5636F, 0x43172F60,
	    0x84C87814, 0xA1F0AB72, 0x8CC70208, 0x1A6439EC,
	    0x90BEFFFA, 0x23631E28, 0xA4506CEB, 0xDE82BDE9,
	    0xBEF9A3F7, 0xB2C67915, 0xC67178F2, 0xE372532B,
	    0xCA273ECE, 0xEA26619C, 0xD186B8C7, 0x21C0C207,
	    0xEADA7DD6, 0xCDE0EB1E, 0xF57D4F7F, 0xEE6ED178,
	    0x06F067AA, 0x72176FBA, 0x0A637DC5, 0xA2C898A6,
	    0x113F9804, 0xBEF90DAE, 0x1B710B35, 0x131C471B,
	    0x28DB77F5, 0x23047D84, 0x32CAAB7B, 0x40C72493,
	    0x3C9EBE0A, 0x15C9BEBC, 0x431D67C4, 0x9C100D4C,
	    0x4CC5D4BE, 0xCB3E42B6, 0x597F299C, 0xFC657E2A,
	    0x5FCB6FAB, 0x3AD6FAEC, 0x6C44198C, 0x4A475817
	  ];

	  var OUTPUT_TYPES = ['hex', 'array', 'digest', 'arrayBuffer'];

	  var blocks = [];

	  if (root.JS_SHA512_NO_NODE_JS || !Array.isArray) {
	    Array.isArray = function (obj) {
	      return Object.prototype.toString.call(obj) === '[object Array]';
	    };
	  }

	  if (ARRAY_BUFFER && (root.JS_SHA512_NO_ARRAY_BUFFER_IS_VIEW || !ArrayBuffer.isView)) {
	    ArrayBuffer.isView = function (obj) {
	      return typeof obj === 'object' && obj.buffer && obj.buffer.constructor === ArrayBuffer;
	    };
	  }

	  var createOutputMethod = function (outputType, bits) {
	    return function (message) {
	      return new Sha512(bits, true).update(message)[outputType]();
	    };
	  };

	  var createMethod = function (bits) {
	    var method = createOutputMethod('hex', bits);
	    method.create = function () {
	      return new Sha512(bits);
	    };
	    method.update = function (message) {
	      return method.create().update(message);
	    };
	    for (var i = 0; i < OUTPUT_TYPES.length; ++i) {
	      var type = OUTPUT_TYPES[i];
	      method[type] = createOutputMethod(type, bits);
	    }
	    return method;
	  };

	  var createHmacOutputMethod = function (outputType, bits) {
	    return function (key, message) {
	      return new HmacSha512(key, bits, true).update(message)[outputType]();
	    };
	  };

	  var createHmacMethod = function (bits) {
	    var method = createHmacOutputMethod('hex', bits);
	    method.create = function (key) {
	      return new HmacSha512(key, bits);
	    };
	    method.update = function (key, message) {
	      return method.create(key).update(message);
	    };
	    for (var i = 0; i < OUTPUT_TYPES.length; ++i) {
	      var type = OUTPUT_TYPES[i];
	      method[type] = createHmacOutputMethod(type, bits);
	    }
	    return method;
	  };

	  function Sha512(bits, sharedMemory) {
	    if (sharedMemory) {
	      blocks[0] = blocks[1] = blocks[2] = blocks[3] = blocks[4] =
	      blocks[5] = blocks[6] = blocks[7] = blocks[8] =
	      blocks[9] = blocks[10] = blocks[11] = blocks[12] =
	      blocks[13] = blocks[14] = blocks[15] = blocks[16] =
	      blocks[17] = blocks[18] = blocks[19] = blocks[20] =
	      blocks[21] = blocks[22] = blocks[23] = blocks[24] =
	      blocks[25] = blocks[26] = blocks[27] = blocks[28] =
	      blocks[29] = blocks[30] = blocks[31] = blocks[32] = 0;
	      this.blocks = blocks;
	    } else {
	      this.blocks = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
	    }

	    if (bits == 384) {
	      this.h0h = 0xCBBB9D5D;
	      this.h0l = 0xC1059ED8;
	      this.h1h = 0x629A292A;
	      this.h1l = 0x367CD507;
	      this.h2h = 0x9159015A;
	      this.h2l = 0x3070DD17;
	      this.h3h = 0x152FECD8;
	      this.h3l = 0xF70E5939;
	      this.h4h = 0x67332667;
	      this.h4l = 0xFFC00B31;
	      this.h5h = 0x8EB44A87;
	      this.h5l = 0x68581511;
	      this.h6h = 0xDB0C2E0D;
	      this.h6l = 0x64F98FA7;
	      this.h7h = 0x47B5481D;
	      this.h7l = 0xBEFA4FA4;
	    } else if (bits == 256) {
	      this.h0h = 0x22312194;
	      this.h0l = 0xFC2BF72C;
	      this.h1h = 0x9F555FA3;
	      this.h1l = 0xC84C64C2;
	      this.h2h = 0x2393B86B;
	      this.h2l = 0x6F53B151;
	      this.h3h = 0x96387719;
	      this.h3l = 0x5940EABD;
	      this.h4h = 0x96283EE2;
	      this.h4l = 0xA88EFFE3;
	      this.h5h = 0xBE5E1E25;
	      this.h5l = 0x53863992;
	      this.h6h = 0x2B0199FC;
	      this.h6l = 0x2C85B8AA;
	      this.h7h = 0x0EB72DDC;
	      this.h7l = 0x81C52CA2;
	    } else if (bits == 224) {
	      this.h0h = 0x8C3D37C8;
	      this.h0l = 0x19544DA2;
	      this.h1h = 0x73E19966;
	      this.h1l = 0x89DCD4D6;
	      this.h2h = 0x1DFAB7AE;
	      this.h2l = 0x32FF9C82;
	      this.h3h = 0x679DD514;
	      this.h3l = 0x582F9FCF;
	      this.h4h = 0x0F6D2B69;
	      this.h4l = 0x7BD44DA8;
	      this.h5h = 0x77E36F73;
	      this.h5l = 0x04C48942;
	      this.h6h = 0x3F9D85A8;
	      this.h6l = 0x6A1D36C8;
	      this.h7h = 0x1112E6AD;
	      this.h7l = 0x91D692A1;
	    } else { // 512
	      this.h0h = 0x6A09E667;
	      this.h0l = 0xF3BCC908;
	      this.h1h = 0xBB67AE85;
	      this.h1l = 0x84CAA73B;
	      this.h2h = 0x3C6EF372;
	      this.h2l = 0xFE94F82B;
	      this.h3h = 0xA54FF53A;
	      this.h3l = 0x5F1D36F1;
	      this.h4h = 0x510E527F;
	      this.h4l = 0xADE682D1;
	      this.h5h = 0x9B05688C;
	      this.h5l = 0x2B3E6C1F;
	      this.h6h = 0x1F83D9AB;
	      this.h6l = 0xFB41BD6B;
	      this.h7h = 0x5BE0CD19;
	      this.h7l = 0x137E2179;
	    }
	    this.bits = bits;

	    this.block = this.start = this.bytes = this.hBytes = 0;
	    this.finalized = this.hashed = false;
	  }

	  Sha512.prototype.update = function (message) {
	    if (this.finalized) {
	      throw new Error(FINALIZE_ERROR);
	    }
	    var notString, type = typeof message;
	    if (type !== 'string') {
	      if (type === 'object') {
	        if (message === null) {
	          throw new Error(INPUT_ERROR);
	        } else if (ARRAY_BUFFER && message.constructor === ArrayBuffer) {
	          message = new Uint8Array(message);
	        } else if (!Array.isArray(message)) {
	          if (!ARRAY_BUFFER || !ArrayBuffer.isView(message)) {
	            throw new Error(INPUT_ERROR);
	          }
	        }
	      } else {
	        throw new Error(INPUT_ERROR);
	      }
	      notString = true;
	    }
	    var code, index = 0, i, length = message.length, blocks = this.blocks;

	    while (index < length) {
	      if (this.hashed) {
	        this.hashed = false;
	        blocks[0] = this.block;
	        blocks[1] = blocks[2] = blocks[3] = blocks[4] =
	        blocks[5] = blocks[6] = blocks[7] = blocks[8] =
	        blocks[9] = blocks[10] = blocks[11] = blocks[12] =
	        blocks[13] = blocks[14] = blocks[15] = blocks[16] =
	        blocks[17] = blocks[18] = blocks[19] = blocks[20] =
	        blocks[21] = blocks[22] = blocks[23] = blocks[24] =
	        blocks[25] = blocks[26] = blocks[27] = blocks[28] =
	        blocks[29] = blocks[30] = blocks[31] = blocks[32] = 0;
	      }

	      if(notString) {
	        for (i = this.start; index < length && i < 128; ++index) {
	          blocks[i >> 2] |= message[index] << SHIFT[i++ & 3];
	        }
	      } else {
	        for (i = this.start; index < length && i < 128; ++index) {
	          code = message.charCodeAt(index);
	          if (code < 0x80) {
	            blocks[i >> 2] |= code << SHIFT[i++ & 3];
	          } else if (code < 0x800) {
	            blocks[i >> 2] |= (0xc0 | (code >> 6)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          } else if (code < 0xd800 || code >= 0xe000) {
	            blocks[i >> 2] |= (0xe0 | (code >> 12)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          } else {
	            code = 0x10000 + (((code & 0x3ff) << 10) | (message.charCodeAt(++index) & 0x3ff));
	            blocks[i >> 2] |= (0xf0 | (code >> 18)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 12) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | ((code >> 6) & 0x3f)) << SHIFT[i++ & 3];
	            blocks[i >> 2] |= (0x80 | (code & 0x3f)) << SHIFT[i++ & 3];
	          }
	        }
	      }

	      this.lastByteIndex = i;
	      this.bytes += i - this.start;
	      if (i >= 128) {
	        this.block = blocks[32];
	        this.start = i - 128;
	        this.hash();
	        this.hashed = true;
	      } else {
	        this.start = i;
	      }
	    }
	    if (this.bytes > 4294967295) {
	      this.hBytes += this.bytes / 4294967296 << 0;
	      this.bytes = this.bytes % 4294967296;
	    }
	    return this;
	  };

	  Sha512.prototype.finalize = function () {
	    if (this.finalized) {
	      return;
	    }
	    this.finalized = true;
	    var blocks = this.blocks, i = this.lastByteIndex;
	    blocks[32] = this.block;
	    blocks[i >> 2] |= EXTRA[i & 3];
	    this.block = blocks[32];
	    if (i >= 112) {
	      if (!this.hashed) {
	        this.hash();
	      }
	      blocks[0] = this.block;
	      blocks[1] = blocks[2] = blocks[3] = blocks[4] =
	      blocks[5] = blocks[6] = blocks[7] = blocks[8] =
	      blocks[9] = blocks[10] = blocks[11] = blocks[12] =
	      blocks[13] = blocks[14] = blocks[15] = blocks[16] =
	      blocks[17] = blocks[18] = blocks[19] = blocks[20] =
	      blocks[21] = blocks[22] = blocks[23] = blocks[24] =
	      blocks[25] = blocks[26] = blocks[27] = blocks[28] =
	      blocks[29] = blocks[30] = blocks[31] = blocks[32] = 0;
	    }
	    blocks[30] = this.hBytes << 3 | this.bytes >>> 29;
	    blocks[31] = this.bytes << 3;
	    this.hash();
	  };

	  Sha512.prototype.hash = function () {
	    var h0h = this.h0h, h0l = this.h0l, h1h = this.h1h, h1l = this.h1l,
	      h2h = this.h2h, h2l = this.h2l, h3h = this.h3h, h3l = this.h3l,
	      h4h = this.h4h, h4l = this.h4l, h5h = this.h5h, h5l = this.h5l,
	      h6h = this.h6h, h6l = this.h6l, h7h = this.h7h, h7l = this.h7l,
	      blocks = this.blocks, j, s0h, s0l, s1h, s1l, c1, c2, c3, c4,
	      abh, abl, dah, dal, cdh, cdl, bch, bcl,
	      majh, majl, t1h, t1l, t2h, t2l, chh, chl;

	    for (j = 32; j < 160; j += 2) {
	      t1h = blocks[j - 30];
	      t1l = blocks[j - 29];
	      s0h = ((t1h >>> 1) | (t1l << 31)) ^ ((t1h >>> 8) | (t1l << 24)) ^ (t1h >>> 7);
	      s0l = ((t1l >>> 1) | (t1h << 31)) ^ ((t1l >>> 8) | (t1h << 24)) ^ ((t1l >>> 7) | t1h << 25);

	      t1h = blocks[j - 4];
	      t1l = blocks[j - 3];
	      s1h = ((t1h >>> 19) | (t1l << 13)) ^ ((t1l >>> 29) | (t1h << 3)) ^ (t1h >>> 6);
	      s1l = ((t1l >>> 19) | (t1h << 13)) ^ ((t1h >>> 29) | (t1l << 3)) ^ ((t1l >>> 6) | t1h << 26);

	      t1h = blocks[j - 32];
	      t1l = blocks[j - 31];
	      t2h = blocks[j - 14];
	      t2l = blocks[j - 13];

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF) + (s0l & 0xFFFF) + (s1l & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (s0l >>> 16) + (s1l >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (s0h & 0xFFFF) + (s1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (s0h >>> 16) + (s1h >>> 16) + (c3 >>> 16);

	      blocks[j] = (c4 << 16) | (c3 & 0xFFFF);
	      blocks[j + 1] = (c2 << 16) | (c1 & 0xFFFF);
	    }

	    var ah = h0h, al = h0l, bh = h1h, bl = h1l, ch = h2h, cl = h2l, dh = h3h, dl = h3l, eh = h4h, el = h4l, fh = h5h, fl = h5l, gh = h6h, gl = h6l, hh = h7h, hl = h7l;
	    bch = bh & ch;
	    bcl = bl & cl;
	    for (j = 0; j < 160; j += 8) {
	      s0h = ((ah >>> 28) | (al << 4)) ^ ((al >>> 2) | (ah << 30)) ^ ((al >>> 7) | (ah << 25));
	      s0l = ((al >>> 28) | (ah << 4)) ^ ((ah >>> 2) | (al << 30)) ^ ((ah >>> 7) | (al << 25));

	      s1h = ((eh >>> 14) | (el << 18)) ^ ((eh >>> 18) | (el << 14)) ^ ((el >>> 9) | (eh << 23));
	      s1l = ((el >>> 14) | (eh << 18)) ^ ((el >>> 18) | (eh << 14)) ^ ((eh >>> 9) | (el << 23));

	      abh = ah & bh;
	      abl = al & bl;
	      majh = abh ^ (ah & ch) ^ bch;
	      majl = abl ^ (al & cl) ^ bcl;

	      chh = (eh & fh) ^ (~eh & gh);
	      chl = (el & fl) ^ (~el & gl);

	      t1h = blocks[j];
	      t1l = blocks[j + 1];
	      t2h = K[j];
	      t2l = K[j + 1];

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF) + (chl & 0xFFFF) + (s1l & 0xFFFF) + (hl & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (chl >>> 16) + (s1l >>> 16) + (hl >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (chh & 0xFFFF) + (s1h & 0xFFFF) + (hh & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (chh >>> 16) + (s1h >>> 16) + (hh >>> 16) + (c3 >>> 16);

	      t1h = (c4 << 16) | (c3 & 0xFFFF);
	      t1l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (majl & 0xFFFF) + (s0l & 0xFFFF);
	      c2 = (majl >>> 16) + (s0l >>> 16) + (c1 >>> 16);
	      c3 = (majh & 0xFFFF) + (s0h & 0xFFFF) + (c2 >>> 16);
	      c4 = (majh >>> 16) + (s0h >>> 16) + (c3 >>> 16);

	      t2h = (c4 << 16) | (c3 & 0xFFFF);
	      t2l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (dl & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (dl >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (dh & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (dh >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      hh = (c4 << 16) | (c3 & 0xFFFF);
	      hl = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      dh = (c4 << 16) | (c3 & 0xFFFF);
	      dl = (c2 << 16) | (c1 & 0xFFFF);

	      s0h = ((dh >>> 28) | (dl << 4)) ^ ((dl >>> 2) | (dh << 30)) ^ ((dl >>> 7) | (dh << 25));
	      s0l = ((dl >>> 28) | (dh << 4)) ^ ((dh >>> 2) | (dl << 30)) ^ ((dh >>> 7) | (dl << 25));

	      s1h = ((hh >>> 14) | (hl << 18)) ^ ((hh >>> 18) | (hl << 14)) ^ ((hl >>> 9) | (hh << 23));
	      s1l = ((hl >>> 14) | (hh << 18)) ^ ((hl >>> 18) | (hh << 14)) ^ ((hh >>> 9) | (hl << 23));

	      dah = dh & ah;
	      dal = dl & al;
	      majh = dah ^ (dh & bh) ^ abh;
	      majl = dal ^ (dl & bl) ^ abl;

	      chh = (hh & eh) ^ (~hh & fh);
	      chl = (hl & el) ^ (~hl & fl);

	      t1h = blocks[j + 2];
	      t1l = blocks[j + 3];
	      t2h = K[j + 2];
	      t2l = K[j + 3];

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF) + (chl & 0xFFFF) + (s1l & 0xFFFF) + (gl & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (chl >>> 16) + (s1l >>> 16) + (gl >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (chh & 0xFFFF) + (s1h & 0xFFFF) + (gh & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (chh >>> 16) + (s1h >>> 16) + (gh >>> 16) + (c3 >>> 16);

	      t1h = (c4 << 16) | (c3 & 0xFFFF);
	      t1l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (majl & 0xFFFF) + (s0l & 0xFFFF);
	      c2 = (majl >>> 16) + (s0l >>> 16) + (c1 >>> 16);
	      c3 = (majh & 0xFFFF) + (s0h & 0xFFFF) + (c2 >>> 16);
	      c4 = (majh >>> 16) + (s0h >>> 16) + (c3 >>> 16);

	      t2h = (c4 << 16) | (c3 & 0xFFFF);
	      t2l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (cl & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (cl >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (ch & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (ch >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      gh = (c4 << 16) | (c3 & 0xFFFF);
	      gl = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      ch = (c4 << 16) | (c3 & 0xFFFF);
	      cl = (c2 << 16) | (c1 & 0xFFFF);

	      s0h = ((ch >>> 28) | (cl << 4)) ^ ((cl >>> 2) | (ch << 30)) ^ ((cl >>> 7) | (ch << 25));
	      s0l = ((cl >>> 28) | (ch << 4)) ^ ((ch >>> 2) | (cl << 30)) ^ ((ch >>> 7) | (cl << 25));

	      s1h = ((gh >>> 14) | (gl << 18)) ^ ((gh >>> 18) | (gl << 14)) ^ ((gl >>> 9) | (gh << 23));
	      s1l = ((gl >>> 14) | (gh << 18)) ^ ((gl >>> 18) | (gh << 14)) ^ ((gh >>> 9) | (gl << 23));

	      cdh = ch & dh;
	      cdl = cl & dl;
	      majh = cdh ^ (ch & ah) ^ dah;
	      majl = cdl ^ (cl & al) ^ dal;

	      chh = (gh & hh) ^ (~gh & eh);
	      chl = (gl & hl) ^ (~gl & el);

	      t1h = blocks[j + 4];
	      t1l = blocks[j + 5];
	      t2h = K[j + 4];
	      t2l = K[j + 5];

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF) + (chl & 0xFFFF) + (s1l & 0xFFFF) + (fl & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (chl >>> 16) + (s1l >>> 16) + (fl >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (chh & 0xFFFF) + (s1h & 0xFFFF) + (fh & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (chh >>> 16) + (s1h >>> 16) + (fh >>> 16) + (c3 >>> 16);

	      t1h = (c4 << 16) | (c3 & 0xFFFF);
	      t1l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (majl & 0xFFFF) + (s0l & 0xFFFF);
	      c2 = (majl >>> 16) + (s0l >>> 16) + (c1 >>> 16);
	      c3 = (majh & 0xFFFF) + (s0h & 0xFFFF) + (c2 >>> 16);
	      c4 = (majh >>> 16) + (s0h >>> 16) + (c3 >>> 16);

	      t2h = (c4 << 16) | (c3 & 0xFFFF);
	      t2l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (bl & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (bl >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (bh & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (bh >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      fh = (c4 << 16) | (c3 & 0xFFFF);
	      fl = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      bh = (c4 << 16) | (c3 & 0xFFFF);
	      bl = (c2 << 16) | (c1 & 0xFFFF);

	      s0h = ((bh >>> 28) | (bl << 4)) ^ ((bl >>> 2) | (bh << 30)) ^ ((bl >>> 7) | (bh << 25));
	      s0l = ((bl >>> 28) | (bh << 4)) ^ ((bh >>> 2) | (bl << 30)) ^ ((bh >>> 7) | (bl << 25));

	      s1h = ((fh >>> 14) | (fl << 18)) ^ ((fh >>> 18) | (fl << 14)) ^ ((fl >>> 9) | (fh << 23));
	      s1l = ((fl >>> 14) | (fh << 18)) ^ ((fl >>> 18) | (fh << 14)) ^ ((fh >>> 9) | (fl << 23));

	      bch = bh & ch;
	      bcl = bl & cl;
	      majh = bch ^ (bh & dh) ^ cdh;
	      majl = bcl ^ (bl & dl) ^ cdl;

	      chh = (fh & gh) ^ (~fh & hh);
	      chl = (fl & gl) ^ (~fl & hl);

	      t1h = blocks[j + 6];
	      t1l = blocks[j + 7];
	      t2h = K[j + 6];
	      t2l = K[j + 7];

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF) + (chl & 0xFFFF) + (s1l & 0xFFFF) + (el & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (chl >>> 16) + (s1l >>> 16) + (el >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (chh & 0xFFFF) + (s1h & 0xFFFF) + (eh & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (chh >>> 16) + (s1h >>> 16) + (eh >>> 16) + (c3 >>> 16);

	      t1h = (c4 << 16) | (c3 & 0xFFFF);
	      t1l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (majl & 0xFFFF) + (s0l & 0xFFFF);
	      c2 = (majl >>> 16) + (s0l >>> 16) + (c1 >>> 16);
	      c3 = (majh & 0xFFFF) + (s0h & 0xFFFF) + (c2 >>> 16);
	      c4 = (majh >>> 16) + (s0h >>> 16) + (c3 >>> 16);

	      t2h = (c4 << 16) | (c3 & 0xFFFF);
	      t2l = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (al & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (al >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (ah & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (ah >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      eh = (c4 << 16) | (c3 & 0xFFFF);
	      el = (c2 << 16) | (c1 & 0xFFFF);

	      c1 = (t2l & 0xFFFF) + (t1l & 0xFFFF);
	      c2 = (t2l >>> 16) + (t1l >>> 16) + (c1 >>> 16);
	      c3 = (t2h & 0xFFFF) + (t1h & 0xFFFF) + (c2 >>> 16);
	      c4 = (t2h >>> 16) + (t1h >>> 16) + (c3 >>> 16);

	      ah = (c4 << 16) | (c3 & 0xFFFF);
	      al = (c2 << 16) | (c1 & 0xFFFF);
	    }

	    c1 = (h0l & 0xFFFF) + (al & 0xFFFF);
	    c2 = (h0l >>> 16) + (al >>> 16) + (c1 >>> 16);
	    c3 = (h0h & 0xFFFF) + (ah & 0xFFFF) + (c2 >>> 16);
	    c4 = (h0h >>> 16) + (ah >>> 16) + (c3 >>> 16);

	    this.h0h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h0l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h1l & 0xFFFF) + (bl & 0xFFFF);
	    c2 = (h1l >>> 16) + (bl >>> 16) + (c1 >>> 16);
	    c3 = (h1h & 0xFFFF) + (bh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h1h >>> 16) + (bh >>> 16) + (c3 >>> 16);

	    this.h1h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h1l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h2l & 0xFFFF) + (cl & 0xFFFF);
	    c2 = (h2l >>> 16) + (cl >>> 16) + (c1 >>> 16);
	    c3 = (h2h & 0xFFFF) + (ch & 0xFFFF) + (c2 >>> 16);
	    c4 = (h2h >>> 16) + (ch >>> 16) + (c3 >>> 16);

	    this.h2h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h2l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h3l & 0xFFFF) + (dl & 0xFFFF);
	    c2 = (h3l >>> 16) + (dl >>> 16) + (c1 >>> 16);
	    c3 = (h3h & 0xFFFF) + (dh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h3h >>> 16) + (dh >>> 16) + (c3 >>> 16);

	    this.h3h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h3l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h4l & 0xFFFF) + (el & 0xFFFF);
	    c2 = (h4l >>> 16) + (el >>> 16) + (c1 >>> 16);
	    c3 = (h4h & 0xFFFF) + (eh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h4h >>> 16) + (eh >>> 16) + (c3 >>> 16);

	    this.h4h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h4l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h5l & 0xFFFF) + (fl & 0xFFFF);
	    c2 = (h5l >>> 16) + (fl >>> 16) + (c1 >>> 16);
	    c3 = (h5h & 0xFFFF) + (fh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h5h >>> 16) + (fh >>> 16) + (c3 >>> 16);

	    this.h5h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h5l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h6l & 0xFFFF) + (gl & 0xFFFF);
	    c2 = (h6l >>> 16) + (gl >>> 16) + (c1 >>> 16);
	    c3 = (h6h & 0xFFFF) + (gh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h6h >>> 16) + (gh >>> 16) + (c3 >>> 16);

	    this.h6h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h6l = (c2 << 16) | (c1 & 0xFFFF);

	    c1 = (h7l & 0xFFFF) + (hl & 0xFFFF);
	    c2 = (h7l >>> 16) + (hl >>> 16) + (c1 >>> 16);
	    c3 = (h7h & 0xFFFF) + (hh & 0xFFFF) + (c2 >>> 16);
	    c4 = (h7h >>> 16) + (hh >>> 16) + (c3 >>> 16);

	    this.h7h = (c4 << 16) | (c3 & 0xFFFF);
	    this.h7l = (c2 << 16) | (c1 & 0xFFFF);
	  };

	  Sha512.prototype.hex = function () {
	    this.finalize();

	    var h0h = this.h0h, h0l = this.h0l, h1h = this.h1h, h1l = this.h1l,
	      h2h = this.h2h, h2l = this.h2l, h3h = this.h3h, h3l = this.h3l,
	      h4h = this.h4h, h4l = this.h4l, h5h = this.h5h, h5l = this.h5l,
	      h6h = this.h6h, h6l = this.h6l, h7h = this.h7h, h7l = this.h7l,
	      bits = this.bits;

	    var hex = HEX_CHARS[(h0h >> 28) & 0x0F] + HEX_CHARS[(h0h >> 24) & 0x0F] +
	      HEX_CHARS[(h0h >> 20) & 0x0F] + HEX_CHARS[(h0h >> 16) & 0x0F] +
	      HEX_CHARS[(h0h >> 12) & 0x0F] + HEX_CHARS[(h0h >> 8) & 0x0F] +
	      HEX_CHARS[(h0h >> 4) & 0x0F] + HEX_CHARS[h0h & 0x0F] +
	      HEX_CHARS[(h0l >> 28) & 0x0F] + HEX_CHARS[(h0l >> 24) & 0x0F] +
	      HEX_CHARS[(h0l >> 20) & 0x0F] + HEX_CHARS[(h0l >> 16) & 0x0F] +
	      HEX_CHARS[(h0l >> 12) & 0x0F] + HEX_CHARS[(h0l >> 8) & 0x0F] +
	      HEX_CHARS[(h0l >> 4) & 0x0F] + HEX_CHARS[h0l & 0x0F] +
	      HEX_CHARS[(h1h >> 28) & 0x0F] + HEX_CHARS[(h1h >> 24) & 0x0F] +
	      HEX_CHARS[(h1h >> 20) & 0x0F] + HEX_CHARS[(h1h >> 16) & 0x0F] +
	      HEX_CHARS[(h1h >> 12) & 0x0F] + HEX_CHARS[(h1h >> 8) & 0x0F] +
	      HEX_CHARS[(h1h >> 4) & 0x0F] + HEX_CHARS[h1h & 0x0F] +
	      HEX_CHARS[(h1l >> 28) & 0x0F] + HEX_CHARS[(h1l >> 24) & 0x0F] +
	      HEX_CHARS[(h1l >> 20) & 0x0F] + HEX_CHARS[(h1l >> 16) & 0x0F] +
	      HEX_CHARS[(h1l >> 12) & 0x0F] + HEX_CHARS[(h1l >> 8) & 0x0F] +
	      HEX_CHARS[(h1l >> 4) & 0x0F] + HEX_CHARS[h1l & 0x0F] +
	      HEX_CHARS[(h2h >> 28) & 0x0F] + HEX_CHARS[(h2h >> 24) & 0x0F] +
	      HEX_CHARS[(h2h >> 20) & 0x0F] + HEX_CHARS[(h2h >> 16) & 0x0F] +
	      HEX_CHARS[(h2h >> 12) & 0x0F] + HEX_CHARS[(h2h >> 8) & 0x0F] +
	      HEX_CHARS[(h2h >> 4) & 0x0F] + HEX_CHARS[h2h & 0x0F] +
	      HEX_CHARS[(h2l >> 28) & 0x0F] + HEX_CHARS[(h2l >> 24) & 0x0F] +
	      HEX_CHARS[(h2l >> 20) & 0x0F] + HEX_CHARS[(h2l >> 16) & 0x0F] +
	      HEX_CHARS[(h2l >> 12) & 0x0F] + HEX_CHARS[(h2l >> 8) & 0x0F] +
	      HEX_CHARS[(h2l >> 4) & 0x0F] + HEX_CHARS[h2l & 0x0F] +
	      HEX_CHARS[(h3h >> 28) & 0x0F] + HEX_CHARS[(h3h >> 24) & 0x0F] +
	      HEX_CHARS[(h3h >> 20) & 0x0F] + HEX_CHARS[(h3h >> 16) & 0x0F] +
	      HEX_CHARS[(h3h >> 12) & 0x0F] + HEX_CHARS[(h3h >> 8) & 0x0F] +
	      HEX_CHARS[(h3h >> 4) & 0x0F] + HEX_CHARS[h3h & 0x0F];
	    if (bits >= 256) {
	      hex += HEX_CHARS[(h3l >> 28) & 0x0F] + HEX_CHARS[(h3l >> 24) & 0x0F] +
	        HEX_CHARS[(h3l >> 20) & 0x0F] + HEX_CHARS[(h3l >> 16) & 0x0F] +
	        HEX_CHARS[(h3l >> 12) & 0x0F] + HEX_CHARS[(h3l >> 8) & 0x0F] +
	        HEX_CHARS[(h3l >> 4) & 0x0F] + HEX_CHARS[h3l & 0x0F];
	    }
	    if (bits >= 384) {
	      hex += HEX_CHARS[(h4h >> 28) & 0x0F] + HEX_CHARS[(h4h >> 24) & 0x0F] +
	        HEX_CHARS[(h4h >> 20) & 0x0F] + HEX_CHARS[(h4h >> 16) & 0x0F] +
	        HEX_CHARS[(h4h >> 12) & 0x0F] + HEX_CHARS[(h4h >> 8) & 0x0F] +
	        HEX_CHARS[(h4h >> 4) & 0x0F] + HEX_CHARS[h4h & 0x0F] +
	        HEX_CHARS[(h4l >> 28) & 0x0F] + HEX_CHARS[(h4l >> 24) & 0x0F] +
	        HEX_CHARS[(h4l >> 20) & 0x0F] + HEX_CHARS[(h4l >> 16) & 0x0F] +
	        HEX_CHARS[(h4l >> 12) & 0x0F] + HEX_CHARS[(h4l >> 8) & 0x0F] +
	        HEX_CHARS[(h4l >> 4) & 0x0F] + HEX_CHARS[h4l & 0x0F] +
	        HEX_CHARS[(h5h >> 28) & 0x0F] + HEX_CHARS[(h5h >> 24) & 0x0F] +
	        HEX_CHARS[(h5h >> 20) & 0x0F] + HEX_CHARS[(h5h >> 16) & 0x0F] +
	        HEX_CHARS[(h5h >> 12) & 0x0F] + HEX_CHARS[(h5h >> 8) & 0x0F] +
	        HEX_CHARS[(h5h >> 4) & 0x0F] + HEX_CHARS[h5h & 0x0F] +
	        HEX_CHARS[(h5l >> 28) & 0x0F] + HEX_CHARS[(h5l >> 24) & 0x0F] +
	        HEX_CHARS[(h5l >> 20) & 0x0F] + HEX_CHARS[(h5l >> 16) & 0x0F] +
	        HEX_CHARS[(h5l >> 12) & 0x0F] + HEX_CHARS[(h5l >> 8) & 0x0F] +
	        HEX_CHARS[(h5l >> 4) & 0x0F] + HEX_CHARS[h5l & 0x0F];
	    }
	    if (bits == 512) {
	      hex += HEX_CHARS[(h6h >> 28) & 0x0F] + HEX_CHARS[(h6h >> 24) & 0x0F] +
	        HEX_CHARS[(h6h >> 20) & 0x0F] + HEX_CHARS[(h6h >> 16) & 0x0F] +
	        HEX_CHARS[(h6h >> 12) & 0x0F] + HEX_CHARS[(h6h >> 8) & 0x0F] +
	        HEX_CHARS[(h6h >> 4) & 0x0F] + HEX_CHARS[h6h & 0x0F] +
	        HEX_CHARS[(h6l >> 28) & 0x0F] + HEX_CHARS[(h6l >> 24) & 0x0F] +
	        HEX_CHARS[(h6l >> 20) & 0x0F] + HEX_CHARS[(h6l >> 16) & 0x0F] +
	        HEX_CHARS[(h6l >> 12) & 0x0F] + HEX_CHARS[(h6l >> 8) & 0x0F] +
	        HEX_CHARS[(h6l >> 4) & 0x0F] + HEX_CHARS[h6l & 0x0F] +
	        HEX_CHARS[(h7h >> 28) & 0x0F] + HEX_CHARS[(h7h >> 24) & 0x0F] +
	        HEX_CHARS[(h7h >> 20) & 0x0F] + HEX_CHARS[(h7h >> 16) & 0x0F] +
	        HEX_CHARS[(h7h >> 12) & 0x0F] + HEX_CHARS[(h7h >> 8) & 0x0F] +
	        HEX_CHARS[(h7h >> 4) & 0x0F] + HEX_CHARS[h7h & 0x0F] +
	        HEX_CHARS[(h7l >> 28) & 0x0F] + HEX_CHARS[(h7l >> 24) & 0x0F] +
	        HEX_CHARS[(h7l >> 20) & 0x0F] + HEX_CHARS[(h7l >> 16) & 0x0F] +
	        HEX_CHARS[(h7l >> 12) & 0x0F] + HEX_CHARS[(h7l >> 8) & 0x0F] +
	        HEX_CHARS[(h7l >> 4) & 0x0F] + HEX_CHARS[h7l & 0x0F];
	    }
	    return hex;
	  };

	  Sha512.prototype.toString = Sha512.prototype.hex;

	  Sha512.prototype.digest = function () {
	    this.finalize();

	    var h0h = this.h0h, h0l = this.h0l, h1h = this.h1h, h1l = this.h1l,
	      h2h = this.h2h, h2l = this.h2l, h3h = this.h3h, h3l = this.h3l,
	      h4h = this.h4h, h4l = this.h4l, h5h = this.h5h, h5l = this.h5l,
	      h6h = this.h6h, h6l = this.h6l, h7h = this.h7h, h7l = this.h7l,
	      bits = this.bits;

	    var arr = [
	      (h0h >> 24) & 0xFF, (h0h >> 16) & 0xFF, (h0h >> 8) & 0xFF, h0h & 0xFF,
	      (h0l >> 24) & 0xFF, (h0l >> 16) & 0xFF, (h0l >> 8) & 0xFF, h0l & 0xFF,
	      (h1h >> 24) & 0xFF, (h1h >> 16) & 0xFF, (h1h >> 8) & 0xFF, h1h & 0xFF,
	      (h1l >> 24) & 0xFF, (h1l >> 16) & 0xFF, (h1l >> 8) & 0xFF, h1l & 0xFF,
	      (h2h >> 24) & 0xFF, (h2h >> 16) & 0xFF, (h2h >> 8) & 0xFF, h2h & 0xFF,
	      (h2l >> 24) & 0xFF, (h2l >> 16) & 0xFF, (h2l >> 8) & 0xFF, h2l & 0xFF,
	      (h3h >> 24) & 0xFF, (h3h >> 16) & 0xFF, (h3h >> 8) & 0xFF, h3h & 0xFF
	    ];

	    if (bits >= 256) {
	      arr.push((h3l >> 24) & 0xFF, (h3l >> 16) & 0xFF, (h3l >> 8) & 0xFF, h3l & 0xFF);
	    }
	    if (bits >= 384) {
	      arr.push(
	        (h4h >> 24) & 0xFF, (h4h >> 16) & 0xFF, (h4h >> 8) & 0xFF, h4h & 0xFF,
	        (h4l >> 24) & 0xFF, (h4l >> 16) & 0xFF, (h4l >> 8) & 0xFF, h4l & 0xFF,
	        (h5h >> 24) & 0xFF, (h5h >> 16) & 0xFF, (h5h >> 8) & 0xFF, h5h & 0xFF,
	        (h5l >> 24) & 0xFF, (h5l >> 16) & 0xFF, (h5l >> 8) & 0xFF, h5l & 0xFF
	      );
	    }
	    if (bits == 512) {
	      arr.push(
	        (h6h >> 24) & 0xFF, (h6h >> 16) & 0xFF, (h6h >> 8) & 0xFF, h6h & 0xFF,
	        (h6l >> 24) & 0xFF, (h6l >> 16) & 0xFF, (h6l >> 8) & 0xFF, h6l & 0xFF,
	        (h7h >> 24) & 0xFF, (h7h >> 16) & 0xFF, (h7h >> 8) & 0xFF, h7h & 0xFF,
	        (h7l >> 24) & 0xFF, (h7l >> 16) & 0xFF, (h7l >> 8) & 0xFF, h7l & 0xFF
	      );
	    }
	    return arr;
	  };

	  Sha512.prototype.array = Sha512.prototype.digest;

	  Sha512.prototype.arrayBuffer = function () {
	    this.finalize();

	    var bits = this.bits;
	    var buffer = new ArrayBuffer(bits / 8);
	    var dataView = new DataView(buffer);
	    dataView.setUint32(0, this.h0h);
	    dataView.setUint32(4, this.h0l);
	    dataView.setUint32(8, this.h1h);
	    dataView.setUint32(12, this.h1l);
	    dataView.setUint32(16, this.h2h);
	    dataView.setUint32(20, this.h2l);
	    dataView.setUint32(24, this.h3h);

	    if (bits >= 256) {
	      dataView.setUint32(28, this.h3l);
	    }
	    if (bits >= 384) {
	      dataView.setUint32(32, this.h4h);
	      dataView.setUint32(36, this.h4l);
	      dataView.setUint32(40, this.h5h);
	      dataView.setUint32(44, this.h5l);
	    }
	    if (bits == 512) {
	      dataView.setUint32(48, this.h6h);
	      dataView.setUint32(52, this.h6l);
	      dataView.setUint32(56, this.h7h);
	      dataView.setUint32(60, this.h7l);
	    }
	    return buffer;
	  };

	  Sha512.prototype.clone = function () {
	    var hash = new Sha512(this.bits, false);
	    this.copyTo(hash);
	    return hash;
	  };

	  Sha512.prototype.copyTo = function (hash) {
	    var i = 0, attrs = [
	      'h0h', 'h0l', 'h1h', 'h1l', 'h2h', 'h2l', 'h3h', 'h3l', 'h4h', 'h4l', 'h5h', 'h5l', 'h6h', 'h6l', 'h7h', 'h7l',
	      'start', 'bytes', 'hBytes', 'finalized', 'hashed', 'lastByteIndex'
	    ];
	    for (i = 0; i < attrs.length; ++i) {
	      hash[attrs[i]] = this[attrs[i]];
	    }
	    for (i = 0; i < this.blocks.length; ++i) {
	      hash.blocks[i] = this.blocks[i];
	    }
	  };

	  function HmacSha512(key, bits, sharedMemory) {
	    var notString, type = typeof key;
	    if (type !== 'string') {
	      if (type === 'object') {
	        if (key === null) {
	          throw new Error(INPUT_ERROR);
	        } else if (ARRAY_BUFFER && key.constructor === ArrayBuffer) {
	          key = new Uint8Array(key);
	        } else if (!Array.isArray(key)) {
	          if (!ARRAY_BUFFER || !ArrayBuffer.isView(key)) {
	            throw new Error(INPUT_ERROR);
	          }
	        }
	      } else {
	        throw new Error(INPUT_ERROR);
	      }
	      notString = true;
	    }
	    var length = key.length;
	    if (!notString) {
	      var bytes = [], length = key.length, index = 0, code;
	      for (var i = 0; i < length; ++i) {
	        code = key.charCodeAt(i);
	        if (code < 0x80) {
	          bytes[index++] = code;
	        } else if (code < 0x800) {
	          bytes[index++] = (0xc0 | (code >> 6));
	          bytes[index++] = (0x80 | (code & 0x3f));
	        } else if (code < 0xd800 || code >= 0xe000) {
	          bytes[index++] = (0xe0 | (code >> 12));
	          bytes[index++] = (0x80 | ((code >> 6) & 0x3f));
	          bytes[index++] = (0x80 | (code & 0x3f));
	        } else {
	          code = 0x10000 + (((code & 0x3ff) << 10) | (key.charCodeAt(++i) & 0x3ff));
	          bytes[index++] = (0xf0 | (code >> 18));
	          bytes[index++] = (0x80 | ((code >> 12) & 0x3f));
	          bytes[index++] = (0x80 | ((code >> 6) & 0x3f));
	          bytes[index++] = (0x80 | (code & 0x3f));
	        }
	      }
	      key = bytes;
	    }

	    if (key.length > 128) {
	      key = (new Sha512(bits, true)).update(key).array();
	    }

	    var oKeyPad = [], iKeyPad = [];
	    for (var i = 0; i < 128; ++i) {
	      var b = key[i] || 0;
	      oKeyPad[i] = 0x5c ^ b;
	      iKeyPad[i] = 0x36 ^ b;
	    }

	    Sha512.call(this, bits, sharedMemory);

	    this.update(iKeyPad);
	    this.oKeyPad = oKeyPad;
	    this.inner = true;
	    this.sharedMemory = sharedMemory;
	  }
	  HmacSha512.prototype = new Sha512();

	  HmacSha512.prototype.finalize = function () {
	    Sha512.prototype.finalize.call(this);
	    if (this.inner) {
	      this.inner = false;
	      var innerHash = this.array();
	      Sha512.call(this, this.bits, this.sharedMemory);
	      this.update(this.oKeyPad);
	      this.update(innerHash);
	      Sha512.prototype.finalize.call(this);
	    }
	  };

	  HmacSha512.prototype.clone = function () {
	    var hash = new HmacSha512([], this.bits, false);
	    this.copyTo(hash);
	    hash.inner = this.inner;
	    for (var i = 0; i < this.oKeyPad.length; ++i) {
	      hash.oKeyPad[i] = this.oKeyPad[i];
	    }
	    return hash;
	  };

	  var exports = createMethod(512);
	  exports.sha512 = exports;
	  exports.sha384 = createMethod(384);
	  exports.sha512_256 = createMethod(256);
	  exports.sha512_224 = createMethod(224);
	  exports.sha512.hmac = createHmacMethod(512);
	  exports.sha384.hmac = createHmacMethod(384);
	  exports.sha512_256.hmac = createHmacMethod(256);
	  exports.sha512_224.hmac = createHmacMethod(224);

	  if (COMMON_JS) {
	    module.exports = exports;
	  } else {
	    root.sha512 = exports.sha512;
	    root.sha384 = exports.sha384;
	    root.sha512_256 = exports.sha512_256;
	    root.sha512_224 = exports.sha512_224;
	  }
	})(); 
} (sha512));

var sha512Exports = sha512.exports;
var hash = /*@__PURE__*/getDefaultExportFromCjs(sha512Exports);

const version = "random/5.7.0";

const logger = new Logger(version);
// Debugging line for testing browser lib in node
//const window = { crypto: { getRandomValues: () => { } } };
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/globalThis
function getGlobal() {
    if (typeof self !== 'undefined') {
        return self;
    }
    if (typeof window !== 'undefined') {
        return window;
    }
    if (typeof global !== 'undefined') {
        return global;
    }
    throw new Error('unable to locate global object');
}
const anyGlobal = getGlobal();
let crypto = anyGlobal.crypto || anyGlobal.msCrypto;
if (!crypto || !crypto.getRandomValues) {
    logger.warn("WARNING: Missing strong random number source");
    crypto = {
        getRandomValues: function (buffer) {
            return logger.throwError("no secure random source avaialble", Logger.errors.UNSUPPORTED_OPERATION, {
                operation: "crypto.getRandomValues"
            });
        }
    };
}
function randomBytes(length) {
    if (length <= 0 || length > 1024 || (length % 1) || length != length) {
        logger.throwArgumentError("invalid length", "length", length);
    }
    const result = new Uint8Array(length);
    crypto.getRandomValues(result);
    return arrayify(result);
}

/**
 * @module @semaphore-protocol/identity
 * @version 3.10.1
 * @file A library to create Semaphore identities.
 * @copyright Ethereum Foundation 2022
 * @license MIT
 * @see [Github]{@link https://github.com/semaphore-protocol/semaphore/tree/main/packages/identity}
*/

var poseidon1$1 = {};

const F = BigInt('21888242871839275222246405745257275088548364400416034343698204186575808495617');
const N_ROUNDS_F = 8;
const N_ROUNDS_P = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
const pow5 = v => {
  let o = v * v;
  return v * o * o % F;
};
function mix(state, M) {
  const out = [];
  for (let x = 0; x < state.length; x++) {
    let o = 0n;
    for (let y = 0; y < state.length; y++) {
      o = o + M[x][y] * state[y];
    }
    out.push(o % F);
  }
  return out;
}
function poseidon(_inputs, opt) {
  const inputs = _inputs.map(i => BigInt(i));
  if (inputs.length <= 0) {
    throw new Error('poseidon-lite: Not enough inputs');
  }
  if (inputs.length > N_ROUNDS_P.length) {
    throw new Error('poseidon-lite: Too many inputs');
  }
  const t = inputs.length + 1;
  const nRoundsF = N_ROUNDS_F;
  const nRoundsP = N_ROUNDS_P[t - 2];
  const {
    C,
    M
  } = opt;
  if (M.length !== t) {
    throw new Error(`poseidon-lite: Incorrect M length, expected ${t} got ${M.length}`);
  }
  let state = [0n, ...inputs];
  for (let x = 0; x < nRoundsF + nRoundsP; x++) {
    for (let y = 0; y < state.length; y++) {
      state[y] = state[y] + C[x * t + y];
      if (x < nRoundsF / 2 || x >= nRoundsF / 2 + nRoundsP) state[y] = pow5(state[y]);else if (y === 0) state[y] = pow5(state[y]);
    }
    state = mix(state, M);
  }
  return state[0];
}
var poseidon_1 = poseidon;

var unstringify = {};

Object.defineProperty(unstringify, "__esModule", {
  value: true
});
unstringify.default = unstringifyBigInts;
function unstringifyBigInts(o) {
  if (Array.isArray(o)) {
    return o.map(unstringifyBigInts);
  } else if (typeof o == 'object') {
    const res = {};
    for (const [key, val] of Object.entries(o)) {
      res[key] = unstringifyBigInts(val);
    }
    return res;
  }
  const byteArray = Uint8Array.from(atob(o), c => c.charCodeAt(0));
  const hex = [...byteArray].map(x => x.toString(16).padStart(2, '0')).join('');
  return BigInt(`0x${hex}`);
}

var _1 = {};

Object.defineProperty(_1, "__esModule", {
  value: true
});
_1.default = void 0;
var _default$1 = {
  C: ['CcRunsaOm9T+H6q6KUy6OKcaoXdTTN0bbH3A29Cr16c=', 'DANWUwiW7sQql+2TfzE1z8UUKzrkBbg0PB2D/6YEy4E=', 'Hiih2TVpitEULlEYK7VM9KAOpaq9Ymi9MX6pd8wVSjA=', 'J68tgxqdJ0gICWXbMOKY5A5XV8PgCNuWTPnisSuRJR8=', 'Hm8RzmD8j1E6ajz+Fq4XWkEpFGLyFM0Iear0NUW3TgM=', 'Kmc4TTu9XkOFQYGctoHwvgRGLtFMNhPY9xkgYmjRQtM=', 'C2b981YJOmEWCfjhL7/s8LmF44HwJRiJNkCPXVyfRdA=', 'AS7j7B541HCDDGEJPCreNwsmyDzFzr7t2qaFLb2wniE=', 'AlK6X2dgv739iPZ/gXXj/WzRxDGwmba7LRCOe0Rbsbk=', 'F5R0zOyl/2dsa+w871QpY1Q5Gok1/3HW71rqrXypMvE=', 'LCQmE3mlG/qSKP9KUD/U7Zwfl0omSWmzfholibvtK5E=', 'HMHXtiaS5j6sLyiL0GlbQ8L2P1AB/A/FU+ZsBVGAGwU=', 'JVBZMBqtqYuy7VX4UpeelgB4Tb8X+6zQXZ7/X9nJG1Y=', 'KEN746wcsuR54fXA7M0ys66iQjSXCoGTsRwpzn5Z79k=', 'KCFqRC8uH3EcpPprU3ZusRhUjaj7T3jUM4diw39fIEM=', 'LB9HzRf6Wt8fOfTnBW3QP+7h784DCUWBEx8jdzI0gsk=', 'B6utArel68SGMrzJNWzrfdna/KJ2Y4pjZGuFZqYhr8k=', 'AjAmRgH/3yknWzP/qrUd/pQp+QiAppzRN9oMTRX5bDw=', 'G8lzBU5R2QWg8WhlZJfKQKhkQUVX7iiecX5dZomaoKk=', 'Lhwi+WRDUAggbDFX6GNB7dJJr/XC2EIfKmsiKI8KZ/w=', 'EiTzjfZ8U3gSHB1fRhu8UJ6OoVmORsn3pwRSvCu6hrg=', 'AuTmnYulnlGSgLS9ntAGj9e/6M2d/toZadKYkYbN4g4=', 'Hx7Mw0qroBN/XfgfwE/z7k8Z7jZOZT8HbUfpc12YAY4=', 'FnKtPXCaNTl0JmwwOamnMRQkRIAyzRgZ6suKTUKE9YI=', 'KD4/3CxuQgxW9Er1GStK6c2mlh8oTSSZHS7WAt+Mj8c=', 'HCo9EgxVDs/Q2wlXFw+gE2g3Ufj9/1nWYU+9af85S8w=', 'IW+Eh3qsYXL3iXpzI0Vu/hQ6mkN3PqbylstrgXdlP70=', 'LA0nK+zyp1dkun6OPijRK86qR+phylmkEaH1FVL5R4g=', 'FuNCmYZcDihITuenTEVOnxcKVICr4FCPy0psPYlUb0M=', 'F1zrpZnpb1s3WiMqb7nMcXcgR3ZYAikPSM2Tl1VIj8U=', 'DHWURA3EjBb+rZ4XWLAoBmqkEL+8NU9U2MX/u0Sh7jI=', 'GjwpvDnyG7XEZtt9frb9j3YOIAE8z5EskkeYgtkZ/Y0=', 'DM/dkG80JuXAmG6gSbJTQAhV00kHT1pmlcjuq80i5o8=', 'FPa8gdnxhvYr20dc5slBGGanqKP9Bls84OaZtn3Z55Y=', 'CWK4J4n7PRKXAspwsvbFqswJmBDJxJXIiO3rc4a5cFI=', 'GogK9wdNGLO/IMed4lEnvBMoSrAe8CV1r+8Mj2oxqG0=', 'EMuhhBmmozLNXnfwIRwVSyCvKST8IP8/TDASu3rpMRs=', 'BX5iqaj4mz69x2umOp6sqPontzGcrjQGdWooSfMC8Q0=', 'KHyXHekdwKvUSt9ThLSYjLlhMDu/Zc/1r6BBO0QoDO4=', 'Id8ziK8Wh7uzvKnaDMqQjx5WK8RtSrpOb395YOMGiR0=', 'G+XIh9JbznA+JcyXTQk0zXid+PcLSY/YPv+LVg4WgrM=', 'Jo2jb3blaPtoEXF1zqLNDdLLXUL9pazqSNWcJwag1cE=', 'DherCR9urlDGCb6vVRDs7MXYu3QTXr0FvQZGDMJqXtY=', 'BNcn5yj/oKZ67lNasHSkMJHvYtjPg9JwBA9cqh9ir0A=', 'DdvXv5wpNBWBtUl2K8Ai7TNwKsEPG/2GKxVBfX45ym4=', 'J5DrM1FiF1J2gWLoKYnGwjT1sNHTr5tYiinEnIeJZUs=', 'HkV8YBpjtz5EcZUBk9ilcDlfPZq4sv0JhLdkIGFC+ek=', 'Ia5kMB3KliVjjWqyu+cTX/qQ7NDEP/kfxMaG/EbgkbA=', 'A3n2PIzjRo1NopMWb0lJKIVL6eNDLglVWFhTTu2NNQs=', 'AC1WQgNZ0CZqdEoICAngVMoOSSGkZoasjJ9YoyTDUEk=', 'EjFY5ZZbXZsdaLPNMuELvtqNYkWeIfQJD8LFr5Y1FaY=', 'C+KfxAhHqUFmHRS79svgQg+7K29Sg21OYMgOtJytnsE=', 'Gslpkd7CuwVXcWFCAVpFPDbbnYWcrV+aIzgC8k/fTBo=', 'FZZEP3Y9vMJfSWT8YdI7Pl4SyfqX8YqSUcozVbywYn4=', 'EuC802VL36drKGHU7Drq4PGFfZ8X5xWu1tBJ6uO6MhI=', 'D8krTxu+qCuepz1K+a8qUM6rrH83FUsZBObHbHz5ZLo=', 'H5wLFhBEZELW8uWSqAE/QLFPfHciI29PnH6WUjOHJ2I=', 'Dr10JErnJnX4zeBhV6eC9AUNkU2ji0wFjRWfZD279NM=', 'LLfw7Tnhbp9pqfr9SrlRwDsGcelzRu45eoOYOdzPxtE=', 'Gp1uLs/wIsxWBUQ+5BurIM52HQUUzlJmkMcrynNS2b8=', 'KhFUOWB/M1peqDw7xEqTMdDBMyapp7owh9oYLWSOxy8=', 'I/m2UptdBA0VuPp67j40EOc4tWMFzUTylTXBFcWkwGA=', 'BYcsFtsPcqIkmsa6SEu5w6POl8FtWLaLJg65OfDm6Kc=', 'EwC97gi7eCTKIPuAEYB19AIZthUdVbXFK2JKfN7d9qc=', 'Gbm2PS8QjhfmOBeGOo9sKI160pkW2YyxBy5Oe31Ss3Y=', 'AVvuE1fjwBW1vaI3ZoUi9hPRyIcmtexCJKIBKEgbT38=', 'KVNzbpS7a58blwek8WFeTv4eHOS6shjL6pLHhbEo/9E=', 'CwaTU7oJFhiGL4BhgMA4X4UbmNNytF9UTOcmbtZgjfw=', 'ME901GHMwTEV5OC8+5OBflWut+uTBrZOT1iKyX2B9Ck=', 'FbvxRs6bygnooz9ed9/k9arSoWSkYXpMuO5UFc3pE/w=', 'CrTf4MJ0LN5EkBAxSHlk7ZuPS4UEBcEMqf8jhZVyyMY=', 'DjLbMgoETjGX9F92SaGWde9e7f6lRt6pJR3jn5Y5d5o=', 'ChdWqh83jKSydjWni2iI5meXczqCd0iWoweO+lFtoBY=', 'BExKM7EPaTRH/RcXf5Uu+JXmHTKPhe+pQlTWoqJdk+8=', 'LtNhG3JbinC+ZVtTf2b3AP4IedeaSWiR03sHtUZsS4s=', 'H5uk6Lq3zkLI7MPXIqouDq3965z900e12DOepxIIWKo=', 'GyMwQwUujCiPfukHqE5RiqOOgqxFAgZtt0BW+GXF09o=', 'JDHhzBZLuNB0Axq3K9VbTJAgU7/A8U2wyi+XsCCHWVQ=', 'CC+TTJH1qsMwzWlToKfbRaE+MiCXWDMZp5Hyc5ZYAf0=', 'K5oKIj51OLCjS+B0MVVCo8dyReKufL6Zmta7kwxImXw=', 'DhzZHt0s+izOuFSDuIepvoFkFj51qKAOsLWJzHAhTn0=', 'Lh6sDyv9/WPJUfYUd+NpiZl3TxmFTQD1iNMkYBzr4vk=', 'DL+pXzf7dAYMdhWOdp1tFXNFeE2O/bM8I9dIEVtQC4M=', 'CPBbO+kj7UTWWtSdimHppnbZkeOndRPZmAwjLfpKT4Q=', 'InGeKgcLzQhSv44hmE0EQ+coSSXcB1ijJaLdUQwEfvY=', 'BB9Zap7hyyvAYPf8w6GrTHvb8DYRmYLA9B9isvJoMMA=', 'Iz/TXeG+UgqHYo6wb2sdTAIb4cLQ3EZKGfzdCYaxD4k=', 'BSS0bRqoel5DJeCkI+vIENMeB4qhtHB+78tFPGHJwmc=', 'LDT0JMgeVxbOR/ysiUuFgkInu5VLDzGZzESGI3xRUhE=', 'C18qS2M4eBkgfv/CtVQfty3SAltUV8yX8zAQMn3kkV4=', 'IiB4VggszFTFty/kOdLP1sF0NdL1evbOrvrEH+BcZZ8=', 'JNV6i/XaY/5OJBWbf4lQtc37IQGUyvefJ4VASM4sgXE=', 'Cvqxgf3V4Fg7Nx11vWk/mDdK1wl7sBqFc5Gbsjt5OW4=', 'LbqbEI8gh3KZilLvrHy9VnbABXGUwWwL8WKQ1isRKO4=', 'JjSbZu24sW9W+IHHiPU/g8u4PeC9WSslWv8T5rzkILM=', 'Ja984OXhA1doXpX5Izl1OtgaVtKOzBk7I1KIo+bxN9s=', 'JbTOe9IpQ5DAlNalXt1ouXDu16roiyv/H3wBh/41AR8=', 'IsVD8Q9siew4flPxkIqI5d6c7yjr3zCxjLnVTB4CtjE=', 'Ajb5PneJxHJPx5CKnxkeHkJekGqRnXo032aOdIgvh6k=', 'KTULQBFmygEOfSfjfQXamWUr2uEU6wFlnLSXr5gMS1I=', 'Du14fWWCDT9r0xu6tUf3WmXtt12ETruJ7hJgkWZSNj8=', 'B8wRcPE7RvIDanU/Ugsykf3NDpm9lCl9GQb2VvTeb60=', 'Irk5IzsdcgX0m89hOj0wsZCHhtf59dEMIFlDVonorOo=', 'AUUXYqCquByKrR3IvDPocHQPCDpaqFQ4rdZQrOYK5aY=', 'I1BrtdhyfURh+r8QJdRtH+MuqmHex9pX5wT+wIkvzok=', 'LkhMROg4rqC6wGrj9xvdCSo3CVMeHv6pf4vWiQc1VSI=', 'D0vH0H66/WQ3nnjFC9LkK69KWUVFztwlRUGNomg1tUw=', 'H008j2WD6eX6dmN4Yvqu6FFYI4hyXfRg5iCZbVDY504=', 'CTUU4McHEfgmYNB74OSpiPrgKrx7aB2RU+uby0j+c4k=', 'GtqwyOKzutNGaZorXzvANkPug+zkcijySljgo0fhU9g=', 'FnKxcmBX2Z3RRwnrtHRkGjeMG5S4ByusGiLb756A2tI=', 'Hf1T1Fdq8uOPRPU/3KtGjMXY4vrgrMTuMNR7I5tHnBQ=', 'DGiIoQt1sPOnCjYmOjfhf+bXfWQPb8PevH8gd1MgXGA=', 'Gt25M6Zb53CSs0p+d9Ev6GEaYeAO5oSLhQkezKnR5Qg=', 'ANdUDc0mioRcEK4Y0d6TPPY4/1Ql8K//eTVijimdF5E=', 'FAwOQmh+nq0BsoJ6VmTKnCb+3eSs2Z2x0xaTnSC4LA4=', 'Lww6EV1DF9GRuom40T0YBsIKD5sk+MXtwJHirlZWWYQ=', 'DE7neP98FFUwBu0iDPnIEAigz/ZwsiuC2MU4odyVjGE=', 'FwTydm1G+Cw2k/AEQMzDYJQk7SbArMZiJ8PXSF3nTGk=', 'Ly0ZzD6l146noCwbUdJEq/B2nJ+FROQCObZv6QCcPPo=', 'GuA4U7dfyrpQU/ES4qjo3N1+5suc/tnH1sdmqAb8Zik=', 'CXGqv3lSQd9R0THQ+mGqXzVWkhstbwFOTkGobdrwVtU=', 'FAjDFuYBThqR1M9rbg3nPtpiT4OA3xyHX1wp97/i9kY=', 'Fmfz/i7b6FAkir5CtUMJO2yJ8fdz7yhTQWkfOYIu9b0=', 'E798XQ0sQ3akiwoDVXzfkVuBcYQJ5cEzQkxpV2UA/jc=', 'B2IKbfsLbOwwFq3z01M8JAJLlTR4VreXGbwLp0OmLCw=', 'FXTH7wxDVF82qMoIvb3YsHXSlZ4vMitzFnXePhmCtNA=', 'Jp5LW3oushr9VnlwpxfO7FvUGEVxwlT9wG4Dp/+DePA='],
  M: [['Bm9vhdb2ioXsEDRTUaI6Oq8H84r4yVKnvOynC9KvetU=', 'K51LQRDJrpl3guFQmx0P2yCnwCu9i+pzBUYrn4Elseg='], ['DMV827CFB9Yr9npEk8wmL7bAnVVwE//x9XP0MSIfj/k=', 'EnTmSaMu01WjGm7WlyThra3oV+hutcOhIbzRR5QyA8g=']]
};
_1.default = _default$1;

Object.defineProperty(poseidon1$1, "__esModule", {
  value: true
});
var poseidon1_2 = poseidon1$1.poseidon1 = poseidon1;
var _poseidon$1 = _interopRequireDefault$1(poseidon_1);
var _unstringify$1 = _interopRequireDefault$1(unstringify);
var _$1 = _interopRequireDefault$1(_1);
function _interopRequireDefault$1(obj) { return obj && obj.__esModule ? obj : { default: obj }; }
const c$1 = (0, _unstringify$1.default)(_$1.default);
function poseidon1(inputs) {
  return (0, _poseidon$1.default)(inputs, c$1);
}

var poseidon2$1 = {};

var _2 = {};

Object.defineProperty(_2, "__esModule", {
  value: true
});
_2.default = void 0;
var _default = {
  C: ['DumlkrqalRjQWYbWVvQMIRTEmTwRuymTjSHUcwTNjm4=', 'APFEUjXyFIxZhlhxafwbzYh7CNTQCGjfVpb/9AlW6GQ=', 'CN/zSH6KyZ4fKaBY0PqAuTDHKHMLerNs6HnziQ7Pc/U=', 'Lye+aQ/a7kbDzij3UysTyFbDU0LIS9puIJZjEPrcAdA=', 'KyrhrPaLe40kFr6/PU9iNLdj/gS4BD7ki4MnvryhbPI=', 'AxnQYgcr737MperAb5fU1VlSwXWrawPq5ktEx9vxHPo=', 'KIE9yuuuqoKKN234evSmO8i3vyetScYpjvezh78oUm0=', 'JydnOyzLyQPxgb844cHUDSAzhlIAw1K8FQkord35y3g=', 'I07EXKJ3J8LnSr0rKhSUzW771D40BYfWuPueMeZcxjI=', 'FbUlNAMa4Y9/hiyyz3z3YKsQqBUKM3sczZn/boeX1Cg=', 'Dcj61tnks19e2aPRhrec444Oio0bWLEy1wHU7s9o0fY=', 'G82V/8IR+8pgD3BfrT+1Z+pOs3j2Lh/sl4BVGKR+TZw=', 'EFILCrchyt/p7/gbAW/DTcdto2wleJN4F8uXjQad5Vk=', 'H21IFJuOf32bJX2O1fu69CkySYB1/tCs6IqeuB9WJ/Y=', 'HZZV9lIwkBTSngDvNaIIm//43ByBbw3JyjS9tUYMhwU=', 'BN9aVv+VvK+wUfexzUOpm6cx/2fkcDIFj+PUGFaXzH0=', 'BnLZlfj/9kAVGz0pDO2vFIaQoQqMhCSn9uwoK25L6Cg=', 'CZlStBSIRFSyEgDX/6/dXwyancwG8nCOn8HYIJtcdbk=', 'BSy6IlXf0Ax8SDFDuo1GlEjkNYaptM2Rg/0OhDprn6Y=', 'C4ut7mkK246wvXRxK3mZr4LeVXByUa13Fgd8uTxGTdw=', 'EZsVkPEzB69aHuZRAgwHx0nBXWBoOoBQuWPQqOSyvdE=', 'AxULfNbV0XslKdNr4PZ7gyxKz8iE707lzhW+C/tKjQk=', 'LMYYLF4UVG488ZUfFzkSNVN077g9gImKvmnLMXyepWU=', 'AFAyVR5jeMRQz+EppASzdkIYyt7awU4rktLNcxEb8Pk=', 'IzI34yibqjS7FH6XLry5UWRpw5n8wGn7iPnaLMKCdrU=', 'Bcj09OvUpuPJgNMWdL++YyMDfyGzSuWk6AwtTCTWAoA=', 'CnsdsTBC05a6BdgYoxnyUlK8817zru2R7h8JslkPxls=', 'KnO3H5shDPWxQpZXLJ0y2/FW4rCG/0fcXfVCNlpATsA=', 'GsmwQXq8yaGTUQfp/8kdw+wY8sTb5/Ipdqdgu1xQxGA=', 'EsAzmuCDdII/q7B2cH70eSafPk1ssQQ0kBXuBG3JP8A=', 'C3R1sQKhZa1/WxjbTh5wT1KQCqMlO6rGgkZoLlbpoo4=', 'A3woSeGRyj7bHF5J9ui4kXyEPjeTZvLqMqs6qI1/hEg=', 'BaaBH4VW8BTpJnRmHiF+m9UgbFyToH3BRf2xdqcWNG8=', 'KaeV59mAKJRulHt11U6fBEB26Hp7KIO0e2de9fOL1m4=', 'IEOaDISzIutFo4V6/Bj1gm6Mc4LIoVhcUHvhmZgf0i8=', 'Lguo2U2ez0qU7CBQxzcf8btQ8neZqEttSipvKgmCyIc=', 'FD/RFc4I+yfKOOt8zoIrRReCLNIQkEjS5tDdzKF9ccg=', 'DGTL7LHHNLhXlo273PgTzfhhFlkyPby/yEMjYjvpyvE=', 'AoowWEfGg/ZG/KklwWP/WudPNI1iwrZw8UJs75QD2lM=', 'Lk71EP8Lb9pfqUCrTEOA8mpry2TYlCe4JNZ1W1254ww=', 'AIHJW8QzhOZj15JwyVbOO4kltPbQM7B4uWOE9QV5QA4=', 'LtXwyRy9l0kYfi+t5ofgXuJJGzScA5oLuoqfQCOguzg=', 'MFCZkfiNo1BLvzdO1ari8DRIoix2I0yMmQ8B8zpzUgY=', 'HD8g/VVAmlMiG3xNSaNWufChEZ+yBntBp1KQlEJOxq0=', 'ELTn86td8AMElRRFm24Y7sRrsiE+jhMeFwiHtH3cuWw=', 'KhmCl5w/9/Q93VQ9iRwqvd2A+ATAd9d1A5qjUC5Dre8=', 'HHTuZPFeHbb+3b6tVtbVXbpDHrw5bJr5XK0PExW9XJE=', 'B1M+yFC6f5jquTA8rOAbS55PLouCcIz6nC/kWgrhRqA=', 'IVdrQ45QBEmhUeTurxexVChcaPQtQsGAihGr83ZMB1A=', 'LxfAVZuP55YIrVyhk9YvELzoOEyBXwkGdD1pMINtSp4=', 'LUd+OGLQdwinnoqulGFwvJd1pCATGEdK5mWwsbficw4=', 'Fi9SQ5ZwZMOQ4JVXeYTyka+6ImbDj1q82Jvg9bJ0fqs=', 'K0yyM+3pukgmTs0siuUNGteoWWqH8p+Kd3enAJI5MxE=', 'LI+8st2Fc9wduvj0YihUd22y7s5thcTPQlTnw14DsHo=', 'HW80dyXkgWry/0U/DNVrGZ4bYen2Aemt5eiNuHCUnak=', 'IEsMOX9OvnHrwtiz31uRPfnmrAK2jTEyTNSa9cRWVSk=', 'DEy53DxP2BdPEUmzxjw8L57LgnzX3CVTT/j7dbx5xQI=', 'F0rWGhRIyJmiVBZHT0kwMB5cSUdSeeBjmmFt3EW8e1Q=', 'GpYXe89NjYn3Wd9OwvPN4uqqKMF3zA+hOpgW1Jo40u8=', 'Bm0EskMx1xzQ74BUvGDE/wUgLBJqIzwagkKs42C4owo=', 'KkxPxuwLDPUhlXgoccbdOzgcxl9y4CrVJwN6Yqob2AQ=', 'E6stE2zPN9RH6fLhSnztyV5yf4RG9tnX5Vr8ASGf1kk=', 'ESFVL8omBhYZ0k2EPcgnacGwT87Cb1UZTC4+hprMapo=', 'AO9lMyKxPWyIm8gXFcN9d6bNJn1ZXEqJCaVUbHyXz/E=', 'DiVIPkWmZSCLJh2Lp0BR5kAMd21lJZXZhFrKNdijl9M=', 'KfU23LnddoIkUmRlnhXYjjlaw9Td6S2MRkSNuXnuuok=', 'KlbvnyxT/rrf2jNXXb29iFoSTieAu+oXDkVrqs4Ppb4=', 'HINhx461z13s+3otF7XECfKuKZmkZ2Lo7kFiQKjLmvE=', 'FRr/XziyCg/ARzCJqvAga4Po5op2RQe/09CrS+dDGcU=', 'BMYYfkHtiB3BsjnIj3+dQ6n1L8jIts3R525HYVtR8QA=', 'E7N72A9NJ/sQ2EMx9vttU0uBxh7RV3ZEnoAbfdycKWc=', 'AaXFNic8LZ31eL+9MsF7eizjZkwqUgMskyHOscToqOQ=', 'KrNWGDTKc4Na0F9desuVC0qaLGZrlybagyI5Blt8OwI=', 'HU2OwpHnINsgD+bWhsDWE6yvavTpXTv2n37VFqWXtkY=', 'BBKU0sxITSKPV4T+eRn9K7klNRJAoEtxFRTJyAtlrx0=', 'FUrJjgFwjGEcT6cVmR8ASJj1eTnRJuOSBClx3ZDoH8Y=', 'CzOdisyn1Pg+7dhAk671EFCzaEyI+LCwRSRWO8bqTaQ=', 'CVXknmYQyUJUpPhM+6s0RZjw5x6v9Kfdge2VtQg5yC4=', 'BnRqYVbrpUQmueIiBvFavKmm9B5vU1xvNSVAHqBlRiY=', 'Dxj1oOzRQjxJbzggxUnCeDjleQ4r0KGWrJF8f/Mgd/s=', 'BPbuyhdR9zCKxZ7/W+smHku1Y1g+3nvJKnOCI9b3bhM=', 'K1aXM2TExPXBo+xNo83OA4gR6xFvs+RbwXaNJvwLN1g=', 'Ejdp3UnVsFTc12uJgEsby44TkrOFcWpdg/62XUN/Ke8=', 'IUe0JPxIyAqI7lK5EWmqzqmJ9kRkcRUJlCV7L7AcY+k=', 'D9wfWFSLhXAabFUF6jMqKWR+bzStQkPC6lStiXzr5U0=', 'Ejc6glH+oATfaKvPD3eG1Lzv8oxdu+DDlE9oXMCgsfI=', 'IeT06l81+FutfqUv90LJ6KZCdWtq9EID3YofNcGpADU=', 'FiQ5FtadLKPftHIiJNTEYrVzZkkvRekNioGTTxvDsUc=', 'HvvkbdeleLT2b5rbyItDeKvCFWbhoEU8oTpBWcrASsI=', 'B+pehTfPXdCIhgIOI6fzh9Ro1VJb5m+FO2csyWqIlpo=', 'BajE+ZaLiqO3tHijD5pbY2UPGadefOEcqf4WwLdsALw=', 'IPBXcSzCFlT7/lm9NF6NrD94GMcBuceILZ1Xtyoy6D8=', 'BKEu3tqd/WiWcvjGf+4xY23NjojQHUkBm9kLM+sz22k=', 'J+iNjBXzfc7kTx5UJaUd7L0TbOUJGmdn5J7JVEzNEBo=', 'L+7Re4QoXtm4pcjF6VpB9m4JZhmncDIjF2xB7kM95NE=', 'HtfMdu30XHxAQkFCD3Kc85TllCkRMSoNaXK4vVOv8rg=', 'FXQumbm/oyMVf/jFhvVmDqxng0dhRM3K3yh0vkVGaxo=', 'GqwoU4f2XoLIlfxoh930BXcQdFTG7AMXKE8DPyfQx4U=', 'JYUcPIRdR5D53a29tgVzV4MuLnpJd19x7HWpZVTWfHc=', 'FaWCFWXMLsLOeEV9sZft81O367osVSM3DdzMPZ8Uamc=', 'JBHVekgTuZgO+n4xodtZZtz2TzYEQndQLxVIXyjHFyc=', 'AC5vjWUgzUcT4zW4wLbS5kfpqY4S9M0lWIKLXvbLTJs=', 'L/e8j0OAzemX2gC2FrD80a+PDpHi/h7XOYg0YJ4DFdI=', 'ALmDG5SFJVle4CckRxvNGC6VIfa3u2jx6Tvk/rsNPL4=', 'Ci9TdouOv2qGkTsOV8BOARykCGSKR0OofXetvwycNRI=', 'ACSBVhQv0Dc6R5+R/yOelg9Zn/fpS+abfyopAwXhGY0=', 'Fx1WILh7+xMoz4wCqz8MmjlxlqpqVCwjUOtRKisrzak=', 'FwpPVVNvfclwCHx8ENb612DJUhct1U3ZnRBF5Ow0qAg=', 'KaujP3mf5mwu8xNK6gQzbsw344wc0hG6SC7KF+Lb+uE=', 'HpvBeaT911j90bsZRQiNR+cNEUoD9qDotbplA2nmSXM=', 'HdJpeZtmD61Y9/SJLfsLWv6q2GmpxLRPnJ4cQ72vjwk=', 'Is28i3ARetFAEYHQLhVFnnzNQm/oacfJXR3Syw8krzg=', 'DvBC5FR3HFM6n1elXFA/zv0xUPUu2Up81bqTucfazv0=', 'EWCeBq1sj+Lyh/MDYDfohRMY6LCKA1mgOzBP/KYugoQ=', 'EWbZ5VRhbbqedT7qQnwXt/7NWMB23+QnCLCPW3g6qa8=', 'LeUpiUMahZWTQTAmNUQT2xd/v0zSrAtW+FWoiDV+5GY=', 'MAbrT/x6hYGabaSS86isHfUa7lsXuOiddL8Bz19x6a0=', 'KvQfu2G6ioD9z2//nj9vQimT/o8KRjn5YjRMgiUUUIY=', 'EZ5oTeR2FV/lprQajryF24cYqyeInoXngbIUus5IJ8M=', 'GDW3huLokl4Yi+pZrjY1N7USSMI4KPBHz/eEuXs/2AA=', 'KCAaNMWU36NNeUmWxkM6INFSusKnkFySbEDihasy7rY=', 'CD79eifRdRCU6A/vr3iwAIZMgutXEYdySnYfiMIsxOc=', 'C2+Io1dxmVJhWOYc7qJ76BHBbfd3TdhRngeVZPYf0Ts=', 'Dsho5tFeUdlkT2bh1kcalFiVEcoA0p4QFDkObuQlT1s=', 'KvM+P4ZncScawMmz7S4RQuzT50uTnNQNANk3q4TJhZE=', 'C1ICEfkEtefQm12WHGrOdzRWjFR91oWLNkzl5HlR8Xg=', 'Cy1yLQkZoarY21jxAGKpLqDFasQnDoIsyiKGIBiKHUA=', 'H3kNTX+M8JTZgM6zfCRT6Ve1SpmRyji74AYdHtblYtQ=', 'AXHrld+/fR6uqXzThfeAFQiFwWI1oqao2pLOsB5QQjM=', 'DC0OO1/VdUkym/aIXaZrm3kLQN79LIZQdiMFOBsWiHM=', 'EWL7KGicJxVOWoIotOcrN3y8r6WJ4oPDXTgDBUQHoY0=', 'LxRZtl3uRBtkrThqkegxDygsWpKonhmSFiPvgklxG8A=', 'Hm/zIWtojD2ZbXQ2fVzUwbxInUZ1TrcSwkP3DRtTz7s=', 'AcqL5zgyuNBoFIfSfRV4AtdBpvNs3CoFdogfkyZHiHU=', 'H3c1cG/+n8WG+XbVvfIj3GgChggLEM6gC5td4xX5ZQ4=', 'JSK2D06jMHZAoMLc4EH7qSGsEKPV8JbvR0XKg4KF8Bk=', 'I/C+4AGxAp1SVQdd3JV/gzQYytT1K2w/jOFsI1VyV1s=', 'K8Gui43buB/KrC1EVV7VaF0UJjPp35BfZtlAEJMILVk=', 'D5QGuCllZKNzBFB7jbo+0WI3EnOgex/JgBH81q1yIF8=', 'I2Co6wzH3vpntymY3pBxThfnWxdKUu5KyxJsjNmV8Kg=', 'FYcaXN3q2XaATIA8uu8lXrSBWl6W34sAbcu8J2f4iUg=', 'GTpWdmmY7p4KhlLdLzsdoDYvT1T3I3lUT5V8ze77Qg8=', 'KjlKQ5NPhpgvm+Vv9PqxcDsuY8itM0g05DCYBed3rg8=', 'GFmVTP64aV8+i2NdyzRRkoks0RIjRDuntBZuiHbA0UI=', 'BOEYF2MFDlgBNETby5nxkCsRvCXZC73KQI04GfT+0ys=', 'D9slPe6Dhp1AwzXqZN6MW7EOuC2wi16LH15VUr/QXyM=', 'BYy+ippQJ72qTvtiOt6tYnXwhobxwImEqdfFuum08cA=', 'E4Ltzplx4YZJfq2xrrH1KyO0uDvvAjqw0VIotMzspZo=', 'A0ZJkPBFxu4IGcpR/RGwvn9huOuZ8Ut34eZjRgHZ6LU=', 'I/e/yHINwpb/8ztB+Y/4PG/KtGBdsutaqlvBN663Clg=', 'ClmhWOPuwhF+bpTn8OnezxjD/9XhUxqSGWNhWLuvYvI=', 'BuxUyAOBwFK1i/I7MS/9POLE66BlQgr49MI+0Adf0Hs=', 'EYhy3IMuDrVHa1ZkjoZ+yLCTQPenvLG0li8P+e0fnQE=', 'E9afoSfYNBZa1cfLp61Z7VLgsPDkLX/qleGQa1IJIbE=', 'FpoXf2PqaBJwscaHenPSG94UOUL7cdxV/YpJ8Z8Qx3s=', 'BO9RWRxurZfvQvKHrc5A2Tq+sDK5IvZv+36aWnRQVE0=', 'JW4XWh3AeTkOzXynA/suOxnsYYBdTwPO1fRe5t0Paew=', 'MBAtKGNqvV/l8q9BL/YAT3XMNg0yBd0toAKBPT4s7rI=', 'EJmOQt/NO78cBxS8c+sb9ARDo/qZvvSjH9Mb4YL8x5I=', 'GT7djp/PPXYl+n0ktZih2J8zYur01YLv7K12+HnjaGA=', 'GBaK/TTy2RXQNozoC3szR9HHpWHOYRQl8mZNeqUfC10=', 'KTg8AevTtqsMAXZW6+ZYtqMo7He8M2JuKeLpWzPqYRE=', 'EGRtLyYD3jmh9K5ed3GmSnAttuhvt2q2AL9XP5AQxxE=', 'C+teB9GycUX1dfE5WlW/Ey+QwltA2ns4ZNAkLcsRF/s=', 'FtaFJSB4wTPcDT7K1itciDD5W7LlS1mr3/vwGNlvozY=', 'Cmq9HYM5OPM8dBVOBAS0tApVW7vsId36/Wct1iBH8Bo=', 'GmefXTbre1yOoSpMLe3I/rEt/+7EUDFycKbxmzTPGGA=', 'CYD7IzvUVsI5dNUODr/eRyakI+raTo9v+8dZLj8bk9Y=', 'FhtCIy5huEy/GBCvk6OPwM7OPVYoySggA+ustcMSxys=', 'CtoQqQx/BSCVD31Hpg1eakk/CXh/FWTl0JID20feGgs=', 'GnMNNyMQuoIyA0WimsQjjtPweoorThIbtQ3bmvQH9FE=', 'LIEg8mjvBU+BcGTDad2n6pCDd/6rpcTf+9oQ71joxVY=', 'HHyIJPdYdT+lfAB4nGhCF7kw6VMTvLc+bnuGSaSWj3A=', 'LNntMfX4aRyOOeQHenT6oPQArYtJHrP3tHsn+j/Rz3c=', 'I/9PnUaBNFfPYNkvV2GDmaXgIqwyHKVQhUriORiiLuo=', 'CZRaXRR6T2bO7OZAXd3Z0K9aLFEDUpQH3/HqWPGAQm0=', 'GI2cUoAl1MK2dmDGt3G5D3x9puqinT8mim3SI+xvxjA=', 'MFDjeZZZa3+B9oMRQx2HNNun2SbTYzWV4MDY3fTw9H8=', 'Fa8RaTloMKkWAMqBAsNcQmzq5UYeP5XYnYKVGNMK/Xg=', 'HabQmIVDLqmgbZ83+HPZhdrpM+NRRmspBChNozINisw=', 'J5bqkNJpryn1+KzzOSESTk5PrT2+ZYlF5UbuQR3aqcs=', 'IC190doPa0sDJcizMHdC8B4VYS7I6TBKfLAxngHTLWA=', 'CW1nkNBbt1kVapUromPWcqLX+ceI9Mgxop2s5MD4vl8=', 'BU76H2Ww/OKDgIllJ12He0ONojzlsT4ZY3mMsUR9JaQ=', 'GxYvg9kX6T7bMwjCmALeudiqaQETsuFIZMz24Y5BZfE=', 'IeUkHhJWTdb9nxzdKg3jnu3+/BRmzFaOxc63RaBQbtw=', 'HPtWYujPWskiaoDuF7Nqvstzq1+H4WGSe0NJ4Q5L3wg=', 'DyEXfjAqdxu65tjR7LNztiyZrzRiIKwBKcU/Zm6yQQA=', 'FnFSI3RgaZKv+w3X9xsSvsQjau3mKQVGvO9+H1FcIyA=', 'D6PsW5SIJZwutM8kUBv62b4uyeQsXMjM1BnSppLK2HA=', 'GTwOBOC9KYNXyyZsFQYIDtNu3OhcZIzAhejFexq1S7o=', 'ECrfjvdHNaJ+kSgwbcvDyZ9vcpHNQGV4zhTqKtq6aPg=', 'D+CveFjkmFnipU1vGtlFsTFqokv73SOuQKbQy3DD6rE=', 'IW9nF7vH3tsIU2oiIIQ/Ti2l8dqp69796KXqc0R5jSI=', 'HaVcyQDw0h9KPmlDkZGKGzwjsqx3PGs++I4uQigyUWE='],
  M: [['EJt/QRug5MmytwyvXDansZS+fBGtJDeL/ttoWSuoEYs=', 'Fu1B4Tu5wMZq4RlCT928vJMU3J/b3upV1sZFQ9xJA+A=', 'K5C7oA/KBYn2F+fcv+guDfcGq2QM6yR7eRqTt042c20='], ['KWnyfu0xpIC5w2x2Q3nbyizI/dFBXD3e1ilAvN4L13E=', 'LiQZ+ewC7DlMmHHIMpY9wbiddDyMe5ZAKbIxFoex/iM=', 'EBBx8AMjebaXMVh2aQ8FPRSNThCfX7BlyKrMVaD4m/o='], ['FDAh7GhqPzMNX55lRjgGXObNeeKMWzdTMmJE7mWhsac=', 'F2zAKWla0CWCpw7/CKb9mdBX4S5Y59e2sWzfq8juKRE=', 'GaP8ClZwK/QXun/uOAJZP6ZERwMHBD93cyec1x0l1eA=']]
};
_2.default = _default;

Object.defineProperty(poseidon2$1, "__esModule", {
  value: true
});
var poseidon2_2 = poseidon2$1.poseidon2 = poseidon2;
var _poseidon = _interopRequireDefault(poseidon_1);
var _unstringify = _interopRequireDefault(unstringify);
var _ = _interopRequireDefault(_2);
function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }
const c = (0, _unstringify.default)(_.default);
function poseidon2(inputs) {
  return (0, _poseidon.default)(inputs, c);
}

function checkParameter(value, name, type) {
    if (typeof value !== type) {
        throw new TypeError("Parameter '".concat(name, "' is not a ").concat(type));
    }
}

/**
 * Generates a random big number.
 * @param numberOfBytes The number of bytes of the number.
 * @returns The generated random number.
 */
function genRandomNumber(numberOfBytes) {
    if (numberOfBytes === void 0) { numberOfBytes = 31; }
    return BigNumber.from(randomBytes(numberOfBytes)).toBigInt();
}
/**
 * Checks if a string is a JSON.
 * @param jsonString The JSON string.
 * @returns True or false.
 */
function isJsonArray(jsonString) {
    try {
        return Array.isArray(JSON.parse(jsonString));
    }
    catch (error) {
        return false;
    }
}

var Identity = /** @class */ (function () {
    /**
     * Initializes the class attributes based on the strategy passed as parameter.
     * @param identityOrMessage Additional data needed to create identity for given strategy.
     */
    function Identity(identityOrMessage) {
        if (identityOrMessage === undefined) {
            this._trapdoor = genRandomNumber();
            this._nullifier = genRandomNumber();
            this._secret = poseidon2_2([this._nullifier, this._trapdoor]);
            this._commitment = poseidon1_2([this._secret]);
            return;
        }
        checkParameter(identityOrMessage, "identityOrMessage", "string");
        if (!isJsonArray(identityOrMessage)) {
            var h = hash.sha512(identityOrMessage).padStart(128, "0");
            // alt_bn128 is 253.6 bits, so we can safely use 253 bits.
            this._trapdoor = BigInt("0x".concat(h.slice(64))) >> BigInt(3);
            this._nullifier = BigInt("0x".concat(h.slice(0, 64))) >> BigInt(3);
            this._secret = poseidon2_2([this._nullifier, this._trapdoor]);
            this._commitment = poseidon1_2([this._secret]);
            return;
        }
        var _a = JSON.parse(identityOrMessage), trapdoor = _a[0], nullifier = _a[1];
        this._trapdoor = BigNumber.from(trapdoor).toBigInt();
        this._nullifier = BigNumber.from(nullifier).toBigInt();
        this._secret = poseidon2_2([this._nullifier, this._trapdoor]);
        this._commitment = poseidon1_2([this._secret]);
    }
    Object.defineProperty(Identity.prototype, "trapdoor", {
        /**
         * Returns the identity trapdoor.
         * @returns The identity trapdoor.
         */
        get: function () {
            return this._trapdoor;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the identity trapdoor.
     * @returns The identity trapdoor.
     */
    Identity.prototype.getTrapdoor = function () {
        return this._trapdoor;
    };
    Object.defineProperty(Identity.prototype, "nullifier", {
        /**
         * Returns the identity nullifier.
         * @returns The identity nullifier.
         */
        get: function () {
            return this._nullifier;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the identity nullifier.
     * @returns The identity nullifier.
     */
    Identity.prototype.getNullifier = function () {
        return this._nullifier;
    };
    Object.defineProperty(Identity.prototype, "secret", {
        /**
         * Returns the identity secret.
         * @returns The identity secret.
         */
        get: function () {
            return this._secret;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the identity secret.
     * @returns The identity secret.
     */
    Identity.prototype.getSecret = function () {
        return this._secret;
    };
    Object.defineProperty(Identity.prototype, "commitment", {
        /**
         * Returns the identity commitment.
         * @returns The identity commitment.
         */
        get: function () {
            return this._commitment;
        },
        enumerable: false,
        configurable: true
    });
    /**
     * Returns the identity commitment.
     * @returns The identity commitment.
     */
    Identity.prototype.getCommitment = function () {
        return this._commitment;
    };
    /**
     * Returns a JSON string with trapdoor and nullifier. It can be used
     * to export the identity and reuse it later.
     * @returns The string representation of the identity.
     */
    Identity.prototype.toString = function () {
        return JSON.stringify(["0x".concat(this._trapdoor.toString(16)), "0x".concat(this._nullifier.toString(16))]);
    };
    return Identity;
}());

const room = {
    id: '123',
    name: 'test',
    roomId: BigInt(7823578923898923898923),
    membership: {
        identityCommitments: [BigInt(123), BigInt(456)]
    }
};
const message = 'hello world';
const identity = new Identity();
console.log(genProof(room, message, identity));
