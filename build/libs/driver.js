// Dafny program Driver.dfy compiled into JavaScript
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const BigNumber = require('bignumber.js');
BigNumber.config({ MODULO_MODE: BigNumber.EUCLID })
let _dafny = (function() {
  let $module = {};
  $module.areEqual = function(a, b) {
    if (typeof a === 'string' && b instanceof _dafny.Seq) {
      // Seq.equals(string) works as expected,
      // and the catch-all else block handles that direction.
      // But the opposite direction doesn't work; handle it here.
      return b.equals(a);
    } else if (typeof a === 'number' && BigNumber.isBigNumber(b)) {
      // This conditional would be correct even without the `typeof a` part,
      // but in most cases it's probably faster to short-circuit on a `typeof`
      // than to call `isBigNumber`. (But it remains to properly test this.)
      return b.isEqualTo(a);
    } else if (typeof a !== 'object' || a === null || b === null) {
      return a === b;
    } else if (BigNumber.isBigNumber(a)) {
      return a.isEqualTo(b);
    } else if (a._tname !== undefined || (Array.isArray(a) && a.constructor.name == "Array")) {
      return a === b;  // pointer equality
    } else {
      return a.equals(b);  // value-type equality
    }
  }
  $module.toString = function(a) {
    if (a === null) {
      return "null";
    } else if (typeof a === "number") {
      return a.toFixed();
    } else if (BigNumber.isBigNumber(a)) {
      return a.toFixed();
    } else if (a._tname !== undefined) {
      return a._tname;
    } else {
      return a.toString();
    }
  }
  $module.escapeCharacter = function(cp) {
    let s = String.fromCodePoint(cp.value)
    switch (s) {
      case '\n': return "\\n";
      case '\r': return "\\r";
      case '\t': return "\\t";
      case '\0': return "\\0";
      case '\'': return "\\'";
      case '\"': return "\\\"";
      case '\\': return "\\\\";
      default: return s;
    };
  }
  $module.NewObject = function() {
    return { _tname: "object" };
  }
  $module.InstanceOfTrait = function(obj, trait) {
    return obj._parentTraits !== undefined && obj._parentTraits().includes(trait);
  }
  $module.Rtd_bool = class {
    static get Default() { return false; }
  }
  $module.Rtd_char = class {
    static get Default() { return 'D'; }  // See CharType.DefaultValue in Dafny source code
  }
  $module.Rtd_codepoint = class {
    static get Default() { return new _dafny.CodePoint('D'.codePointAt(0)); }
  }
  $module.Rtd_int = class {
    static get Default() { return BigNumber(0); }
  }
  $module.Rtd_number = class {
    static get Default() { return 0; }
  }
  $module.Rtd_ref = class {
    static get Default() { return null; }
  }
  $module.Rtd_array = class {
    static get Default() { return []; }
  }
  $module.ZERO = new BigNumber(0);
  $module.ONE = new BigNumber(1);
  $module.NUMBER_LIMIT = new BigNumber(0x20).multipliedBy(0x1000000000000);  // 2^53
  $module.Tuple = class Tuple extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return "(" + arrayElementsToString(this) + ")";
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      for (let i = 0; i < this.length; i++) {
        if (!_dafny.areEqual(this[i], other[i])) {
          return false;
        }
      }
      return true;
    }
    static Default(...values) {
      return Tuple.of(...values);
    }
    static Rtd(...rtdArgs) {
      return {
        Default: Tuple.from(rtdArgs, rtd => rtd.Default)
      };
    }
  }
  $module.Set = class Set extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return Set.Empty;
    }
    toString() {
      return "{" + arrayElementsToString(this) + "}";
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new Set();
      }
      return this._empty;
    }
    static fromElements(...elmts) {
      let s = new Set();
      for (let k of elmts) {
        s.add(k);
      }
      return s;
    }
    contains(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i], k)) {
          return true;
        }
      }
      return false;
    }
    add(k) {  // mutates the Set; use only during construction
      if (!this.contains(k)) {
        this.push(k);
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let e of this) {
        if (!other.contains(e)) {
          return false;
        }
      }
      return true;
    }
    get Elements() {
      return this;
    }
    Union(that) {
      if (this.length === 0) {
        return that;
      } else if (that.length === 0) {
        return this;
      } else {
        let s = Set.of(...this);
        for (let k of that) {
          s.add(k);
        }
        return s;
      }
    }
    Intersect(that) {
      if (this.length === 0) {
        return this;
      } else if (that.length === 0) {
        return that;
      } else {
        let s = new Set();
        for (let k of this) {
          if (that.contains(k)) {
            s.push(k);
          }
        }
        return s;
      }
    }
    Difference(that) {
      if (this.length == 0 || that.length == 0) {
        return this;
      } else {
        let s = new Set();
        for (let k of this) {
          if (!that.contains(k)) {
            s.push(k);
          }
        }
        return s;
      }
    }
    IsDisjointFrom(that) {
      for (let k of this) {
        if (that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    IsSubsetOf(that) {
      if (that.length < this.length) {
        return false;
      }
      for (let k of this) {
        if (!that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    IsProperSubsetOf(that) {
      if (that.length <= this.length) {
        return false;
      }
      for (let k of this) {
        if (!that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    get AllSubsets() {
      return this.AllSubsets_();
    }
    *AllSubsets_() {
      // Start by putting all set elements into a list, but don't include null
      let elmts = Array.of(...this);
      let n = elmts.length;
      let which = new Array(n);
      which.fill(false);
      let a = [];
      while (true) {
        yield Set.of(...a);
        // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "a".
        let i = 0;
        for (; i < n && which[i]; i++) {
          which[i] = false;
          // remove elmts[i] from a
          for (let j = 0; j < a.length; j++) {
            if (_dafny.areEqual(a[j], elmts[i])) {
              // move the last element of a into slot j
              a[j] = a[-1];
              a.pop();
              break;
            }
          }
        }
        if (i === n) {
          // we have cycled through all the subsets
          break;
        }
        which[i] = true;
        a.push(elmts[i]);
      }
    }
  }
  $module.MultiSet = class MultiSet extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return MultiSet.Empty;
    }
    toString() {
      let s = "multiset{";
      let sep = "";
      for (let e of this) {
        let [k, n] = e;
        let ks = _dafny.toString(k);
        while (!n.isZero()) {
          n = n.minus(1);
          s += sep + ks;
          sep = ", ";
        }
      }
      s += "}";
      return s;
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new MultiSet();
      }
      return this._empty;
    }
    static fromElements(...elmts) {
      let s = new MultiSet();
      for (let e of elmts) {
        s.add(e, _dafny.ONE);
      }
      return s;
    }
    static FromArray(arr) {
      let s = new MultiSet();
      for (let e of arr) {
        s.add(e, _dafny.ONE);
      }
      return s;
    }
    cardinality() {
      let c = _dafny.ZERO;
      for (let e of this) {
        let [k, n] = e;
        c = c.plus(n);
      }
      return c;
    }
    clone() {
      let s = new MultiSet();
      for (let e of this) {
        let [k, n] = e;
        s.push([k, n]);  // make sure to create a new array [k, n] here
      }
      return s;
    }
    findIndex(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i][0], k)) {
          return i;
        }
      }
      return this.length;
    }
    get(k) {
      let i = this.findIndex(k);
      if (i === this.length) {
        return _dafny.ZERO;
      } else {
        return this[i][1];
      }
    }
    contains(k) {
      return !this.get(k).isZero();
    }
    add(k, n) {
      let i = this.findIndex(k);
      if (i === this.length) {
        this.push([k, n]);
      } else {
        let m = this[i][1];
        this[i] = [k, m.plus(n)];
      }
    }
    update(k, n) {
      let i = this.findIndex(k);
      if (i < this.length && this[i][1].isEqualTo(n)) {
        return this;
      } else if (i === this.length && n.isZero()) {
        return this;
      } else if (i === this.length) {
        let m = this.slice();
        m.push([k, n]);
        return m;
      } else {
        let m = this.slice();
        m[i] = [k, n];
        return m;
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      for (let e of this) {
        let [k, n] = e;
        let m = other.get(k);
        if (!n.isEqualTo(m)) {
          return false;
        }
      }
      return this.cardinality().isEqualTo(other.cardinality());
    }
    get Elements() {
      return this.Elements_();
    }
    *Elements_() {
      for (let i = 0; i < this.length; i++) {
        let [k, n] = this[i];
        while (!n.isZero()) {
          yield k;
          n = n.minus(1);
        }
      }
    }
    get UniqueElements() {
      return this.UniqueElements_();
    }
    *UniqueElements_() {
      for (let e of this) {
        let [k, n] = e;
        if (!n.isZero()) {
          yield k;
        }
      }
    }
    Union(that) {
      if (this.length === 0) {
        return that;
      } else if (that.length === 0) {
        return this;
      } else {
        let s = this.clone();
        for (let e of that) {
          let [k, n] = e;
          s.add(k, n);
        }
        return s;
      }
    }
    Intersect(that) {
      if (this.length === 0) {
        return this;
      } else if (that.length === 0) {
        return that;
      } else {
        let s = new MultiSet();
        for (let e of this) {
          let [k, n] = e;
          let m = that.get(k);
          if (!m.isZero()) {
            s.push([k, m.isLessThan(n) ? m : n]);
          }
        }
        return s;
      }
    }
    Difference(that) {
      if (this.length === 0 || that.length === 0) {
        return this;
      } else {
        let s = new MultiSet();
        for (let e of this) {
          let [k, n] = e;
          let d = n.minus(that.get(k));
          if (d.isGreaterThan(0)) {
            s.push([k, d]);
          }
        }
        return s;
      }
    }
    IsDisjointFrom(that) {
      let intersection = this.Intersect(that);
      return intersection.cardinality().isZero();
    }
    IsSubsetOf(that) {
      for (let e of this) {
        let [k, n] = e;
        let m = that.get(k);
        if (!n.isLessThanOrEqualTo(m)) {
          return false;
        }
      }
      return true;
    }
    IsProperSubsetOf(that) {
      return this.IsSubsetOf(that) && this.cardinality().isLessThan(that.cardinality());
    }
  }
  $module.CodePoint = class CodePoint {
    constructor(value) {
      this.value = value
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      return this.value === other.value
    }
    isLessThan(other) {
      return this.value < other.value
    }
    isLessThanOrEqual(other) {
      return this.value <= other.value
    }
    toString() {
      return "'" + $module.escapeCharacter(this) + "'";
    }
  }
  $module.Seq = class Seq extends Array {
    constructor(...elems) {
      super(...elems);
    }
    static get Default() {
      return Seq.of();
    }
    static Create(n, init) {
      return Seq.from({length: n}, (_, i) => init(new BigNumber(i)));
    }
    static UnicodeFromString(s) {
      return new Seq(...([...s].map(c => new _dafny.CodePoint(c.codePointAt(0)))))
    }
    toString() {
      return "[" + arrayElementsToString(this) + "]";
    }
    toVerbatimString(asLiteral) {
      if (asLiteral) {
        return '"' + this.map(c => _dafny.escapeCharacter(c)).join("") + '"';
      } else {
        return this.map(c => String.fromCodePoint(c.value)).join("");
      }
    }
    static update(s, i, v) {
      if (typeof s === "string") {
        let p = s.slice(0, i);
        let q = s.slice(i.toNumber() + 1);
        return p.concat(v, q);
      } else {
        let t = s.slice();
        t[i] = v;
        return t;
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let i = 0; i < this.length; i++) {
        if (!_dafny.areEqual(this[i], other[i])) {
          return false;
        }
      }
      return true;
    }
    static contains(s, k) {
      if (typeof s === "string") {
        return s.includes(k);
      } else {
        for (let x of s) {
          if (_dafny.areEqual(x, k)) {
            return true;
          }
        }
        return false;
      }
    }
    get Elements() {
      return this;
    }
    get UniqueElements() {
      return _dafny.Set.fromElements(...this);
    }
    static Concat(a, b) {
      if (typeof a === "string" || typeof b === "string") {
        // string concatenation, so make sure both operands are strings before concatenating
        if (typeof a !== "string") {
          // a must be a Seq
          a = a.join("");
        }
        if (typeof b !== "string") {
          // b must be a Seq
          b = b.join("");
        }
        return a + b;
      } else {
        // ordinary concatenation
        let r = Seq.of(...a);
        r.push(...b);
        return r;
      }
    }
    static JoinIfPossible(x) {
      try { return x.join(""); } catch(_error) { return x; }
    }
    static IsPrefixOf(a, b) {
      if (b.length < a.length) {
        return false;
      }
      for (let i = 0; i < a.length; i++) {
        if (!_dafny.areEqual(a[i], b[i])) {
          return false;
        }
      }
      return true;
    }
    static IsProperPrefixOf(a, b) {
      if (b.length <= a.length) {
        return false;
      }
      for (let i = 0; i < a.length; i++) {
        if (!_dafny.areEqual(a[i], b[i])) {
          return false;
        }
      }
      return true;
    }
  }
  $module.Map = class Map extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return Map.of();
    }
    toString() {
      return "map[" + this.map(maplet => _dafny.toString(maplet[0]) + " := " + _dafny.toString(maplet[1])).join(", ") + "]";
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new Map();
      }
      return this._empty;
    }
    findIndex(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i][0], k)) {
          return i;
        }
      }
      return this.length;
    }
    get(k) {
      let i = this.findIndex(k);
      if (i === this.length) {
        return undefined;
      } else {
        return this[i][1];
      }
    }
    contains(k) {
      return this.findIndex(k) < this.length;
    }
    update(k, v) {
      let m = this.slice();
      m.updateUnsafe(k, v);
      return m;
    }
    // Similar to update, but make the modification in-place.
    // Meant to be used in the map constructor.
    updateUnsafe(k, v) {
      let m = this;
      let i = m.findIndex(k);
      m[i] = [k, v];
      return m;
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let e of this) {
        let [k, v] = e;
        let w = other.get(k);
        if (w === undefined || !_dafny.areEqual(v, w)) {
          return false;
        }
      }
      return true;
    }
    get Keys() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.push(k);
      }
      return s;
    }
    get Values() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.add(v);
      }
      return s;
    }
    get Items() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.push(_dafny.Tuple.of(k, v));
      }
      return s;
    }
    Merge(that) {
      let m = that.slice();
      for (let e of this) {
        let [k, v] = e;
        let i = m.findIndex(k);
        if (i == m.length) {
          m[i] = [k, v];
        }
      }
      return m;
    }
    Subtract(keys) {
      if (this.length === 0 || keys.length === 0) {
        return this;
      }
      let m = new Map();
      for (let e of this) {
        let [k, v] = e;
        if (!keys.contains(k)) {
          m[m.length] = e;
        }
      }
      return m;
    }
  }
  $module.newArray = function(initValue, ...dims) {
    return { dims: dims, elmts: buildArray(initValue, ...dims) };
  }
  $module.BigOrdinal = class BigOrdinal {
    static get Default() {
      return _dafny.ZERO;
    }
    static IsLimit(ord) {
      return ord.isZero();
    }
    static IsSucc(ord) {
      return ord.isGreaterThan(0);
    }
    static Offset(ord) {
      return ord;
    }
    static IsNat(ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }
  $module.BigRational = class BigRational {
    static get ZERO() {
      if (this._zero === undefined) {
        this._zero = new BigRational(_dafny.ZERO);
      }
      return this._zero;
    }
    constructor (n, d) {
      // requires d === undefined || 1 <= d
      this.num = n;
      this.den = d === undefined ? _dafny.ONE : d;
      // invariant 1 <= den || (num == 0 && den == 0)
    }
    static get Default() {
      return _dafny.BigRational.ZERO;
    }
    // We need to deal with the special case `num == 0 && den == 0`, because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore `den` when `num` is 0.
    toString() {
      if (this.num.isZero() || this.den.isEqualTo(1)) {
        return this.num.toFixed() + ".0";
      }
      let answer = this.dividesAPowerOf10(this.den);
      if (answer !== undefined) {
        let n = this.num.multipliedBy(answer[0]);
        let log10 = answer[1];
        let sign, digits;
        if (this.num.isLessThan(0)) {
          sign = "-"; digits = n.negated().toFixed();
        } else {
          sign = ""; digits = n.toFixed();
        }
        if (log10 < digits.length) {
          let digitCount = digits.length - log10;
          return sign + digits.slice(0, digitCount) + "." + digits.slice(digitCount);
        } else {
          return sign + "0." + "0".repeat(log10 - digits.length) + digits;
        }
      } else {
        return "(" + this.num.toFixed() + ".0 / " + this.den.toFixed() + ".0)";
      }
    }
    isPowerOf10(x) {
      if (x.isZero()) {
        return undefined;
      }
      let log10 = 0;
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.isEqualTo(1)) {
          return log10;
        } else if (x.mod(10).isZero()) {
          log10++;
          x = x.dividedToIntegerBy(10);
        } else {
          return undefined;
        }
      }
    }
    dividesAPowerOf10(i) {
      let factor = _dafny.ONE;
      let log10 = 0;
      if (i.isLessThanOrEqualTo(_dafny.ZERO)) {
        return undefined;
      }

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i.mod(10).isZero()) {
        i = i.dividedToIntegerBy(10);
       log10++;
      }

      while (i.mod(5).isZero()) {
        i = i.dividedToIntegerBy(5);
        factor = factor.multipliedBy(2);
        log10++;
      }
      while (i.mod(2).isZero()) {
        i = i.dividedToIntegerBy(2);
        factor = factor.multipliedBy(5);
        log10++;
      }

      if (i.isEqualTo(_dafny.ONE)) {
        return [factor, log10];
      } else {
        return undefined;
      }
}
    toBigNumber() {
      if (this.num.isZero() || this.den.isEqualTo(1)) {
        return this.num;
      } else if (this.num.isGreaterThan(0)) {
        return this.num.dividedToIntegerBy(this.den);
      } else {
        return this.num.minus(this.den).plus(1).dividedToIntegerBy(this.den);
      }
    }
    // Returns values such that aa/dd == a and bb/dd == b.
    normalize(b) {
      let a = this;
      let aa, bb, dd;
      if (a.num.isZero()) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.isZero()) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        let gcd = BigNumberGcd(a.den, b.den);
        let xx = a.den.dividedToIntegerBy(gcd);
        let yy = b.den.dividedToIntegerBy(gcd);
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num.multipliedBy(yy);
        bb = b.num.multipliedBy(xx);
        dd = a.den.multipliedBy(yy);
      }
      return [aa, bb, dd];
    }
    compareTo(that) {
      // simple things first
      let asign = this.num.isZero() ? 0 : this.num.isLessThan(0) ? -1 : 1;
      let bsign = that.num.isZero() ? 0 : that.num.isLessThan(0) ? -1 : 1;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      let [aa, bb, dd] = this.normalize(that);
      if (aa.isLessThan(bb)) {
        return -1;
      } else if (aa.isEqualTo(bb)){
        return 0;
      } else {
        return 1;
      }
    }
    equals(that) {
      return this.compareTo(that) === 0;
    }
    isLessThan(that) {
      return this.compareTo(that) < 0;
    }
    isAtMost(that) {
      return this.compareTo(that) <= 0;
    }
    plus(b) {
      let [aa, bb, dd] = this.normalize(b);
      return new BigRational(aa.plus(bb), dd);
    }
    minus(b) {
      let [aa, bb, dd] = this.normalize(b);
      return new BigRational(aa.minus(bb), dd);
    }
    negated() {
      return new BigRational(this.num.negated(), this.den);
    }
    multipliedBy(b) {
      return new BigRational(this.num.multipliedBy(b.num), this.den.multipliedBy(b.den));
    }
    dividedBy(b) {
      let a = this;
      // Compute the reciprocal of b
      let bReciprocal;
      if (b.num.isGreaterThan(0)) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(b.den.negated(), b.num.negated());
      }
      return a.multipliedBy(bReciprocal);
    }
  }
  $module.EuclideanDivisionNumber = function(a, b) {
    if (0 <= a) {
      if (0 <= b) {
        // +a +b: a/b
        return Math.floor(a / b);
      } else {
        // +a -b: -(a/(-b))
        return -Math.floor(a / -b);
      }
    } else {
      if (0 <= b) {
        // -a +b: -((-a-1)/b) - 1
        return -Math.floor((-a-1) / b) - 1;
      } else {
        // -a -b: ((-a-1)/(-b)) + 1
        return Math.floor((-a-1) / -b) + 1;
      }
    }
  }
  $module.EuclideanDivision = function(a, b) {
    if (a.isGreaterThanOrEqualTo(0)) {
      if (b.isGreaterThanOrEqualTo(0)) {
        // +a +b: a/b
        return a.dividedToIntegerBy(b);
      } else {
        // +a -b: -(a/(-b))
        return a.dividedToIntegerBy(b.negated()).negated();
      }
    } else {
      if (b.isGreaterThanOrEqualTo(0)) {
        // -a +b: -((-a-1)/b) - 1
        return a.negated().minus(1).dividedToIntegerBy(b).negated().minus(1);
      } else {
        // -a -b: ((-a-1)/(-b)) + 1
        return a.negated().minus(1).dividedToIntegerBy(b.negated()).plus(1);
      }
    }
  }
  $module.EuclideanModuloNumber = function(a, b) {
    let bp = Math.abs(b);
    if (0 <= a) {
      // +a: a % bp
      return a % bp;
    } else {
      // c = ((-a) % bp)
      // -a: bp - c if c > 0
      // -a: 0 if c == 0
      let c = (-a) % bp;
      return c === 0 ? c : bp - c;
    }
  }
  $module.ShiftLeft = function(b, n) {
    return b.multipliedBy(new BigNumber(2).exponentiatedBy(n));
  }
  $module.ShiftRight = function(b, n) {
    return b.dividedToIntegerBy(new BigNumber(2).exponentiatedBy(n));
  }
  $module.RotateLeft = function(b, n, w) {  // truncate(b << n) | (b >> (w - n))
    let x = _dafny.ShiftLeft(b, n).mod(new BigNumber(2).exponentiatedBy(w));
    let y = _dafny.ShiftRight(b, w - n);
    return x.plus(y);
  }
  $module.RotateRight = function(b, n, w) {  // (b >> n) | truncate(b << (w - n))
    let x = _dafny.ShiftRight(b, n);
    let y = _dafny.ShiftLeft(b, w - n).mod(new BigNumber(2).exponentiatedBy(w));;
    return x.plus(y);
  }
  $module.BitwiseAnd = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 & b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    return r;
  }
  $module.BitwiseOr = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 | b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    r = r.plus(h.multipliedBy(a | b));
    return r;
  }
  $module.BitwiseXor = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 ^ b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    r = r.plus(h.multipliedBy(a | b));
    return r;
  }
  $module.BitwiseNot = function(a, bits) {
    let r = _dafny.ZERO;
    let h = _dafny.ONE;
    for (let i = 0; i < bits; i++) {
      let bit = a.mod(2);
      if (bit.isZero()) {
        r = r.plus(h);
      }
      a = a.dividedToIntegerBy(2);
      h = h.multipliedBy(2);
    }
    return r;
  }
  $module.Quantifier = function(vals, frall, pred) {
    for (let u of vals) {
      if (pred(u) !== frall) { return !frall; }
    }
    return frall;
  }
  $module.PlusChar = function(a, b) {
    return String.fromCharCode(a.charCodeAt(0) + b.charCodeAt(0));
  }
  $module.UnicodePlusChar = function(a, b) {
    return new _dafny.CodePoint(a.value + b.value);
  }
  $module.MinusChar = function(a, b) {
    return String.fromCharCode(a.charCodeAt(0) - b.charCodeAt(0));
  }
  $module.UnicodeMinusChar = function(a, b) {
    return new _dafny.CodePoint(a.value - b.value);
  }
  $module.AllBooleans = function*() {
    yield false;
    yield true;
  }
  $module.AllChars = function*() {
    for (let i = 0; i < 0x10000; i++) {
      yield String.fromCharCode(i);
    }
  }
  $module.AllUnicodeChars = function*() {
    for (let i = 0; i < 0xD800; i++) {
      yield new _dafny.CodePoint(i);
    }
    for (let i = 0xE0000; i < 0x110000; i++) {
      yield new _dafny.CodePoint(i);
    }
  }
  $module.AllIntegers = function*() {
    yield _dafny.ZERO;
    for (let j = _dafny.ONE;; j = j.plus(1)) {
      yield j;
      yield j.negated();
    }
  }
  $module.IntegerRange = function*(lo, hi) {
    if (lo === null) {
      while (true) {
        hi = hi.minus(1);
        yield hi;
      }
    } else if (hi === null) {
      while (true) {
        yield lo;
        lo = lo.plus(1);
      }
    } else {
      while (lo.isLessThan(hi)) {
        yield lo;
        lo = lo.plus(1);
      }
    }
  }
  $module.SingleValue = function*(v) {
    yield v;
  }
  $module.HaltException = class HaltException extends Error {
    constructor(message) {
      super(message)
    }
  }
  $module.HandleHaltExceptions = function(f) {
    try {
      f()
    } catch (e) {
      if (e instanceof _dafny.HaltException) {
        process.stdout.write("[Program halted] " + e.message + "\n")
        process.exitCode = 1
      } else {
        throw e
      }
    }
  }
  $module.FromMainArguments = function(args) {
    var a = [...args];
    a.splice(0, 2, args[0] + " " + args[1]);
    return a;
  }
  $module.UnicodeFromMainArguments = function(args) {
    return $module.FromMainArguments(args).map(_dafny.Seq.UnicodeFromString);
  }
  return $module;

  // What follows are routines private to the Dafny runtime
  function buildArray(initValue, ...dims) {
    if (dims.length === 0) {
      return initValue;
    } else {
      let a = Array(dims[0].toNumber());
      let b = Array.from(a, (x) => buildArray(initValue, ...dims.slice(1)));
      return b;
    }
  }
  function arrayElementsToString(a) {
    // like `a.join(", ")`, but calling _dafny.toString(x) on every element x instead of x.toString()
    let s = "";
    let sep = "";
    for (let x of a) {
      s += sep + _dafny.toString(x);
      sep = ", ";
    }
    return s;
  }
  function BigNumberGcd(a, b){  // gcd of two non-negative BigNumber's
    while (true) {
      if (a.isZero()) {
        return b;
      } else if (b.isZero()) {
        return a;
      }
      if (a.isLessThan(b)) {
        b = b.modulo(a);
      } else {
        a = a.modulo(b);
      }
    }
  }
})();
let _System = (function() {
  let $module = {};

  $module.nat = class nat {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module _System
let Int = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Int._default";
    }
    _parentTraits() {
      return [];
    }
    static Abs(x) {
      if ((_dafny.ZERO).isLessThanOrEqualTo(x)) {
        return x;
      } else {
        return (_dafny.ZERO).minus(x);
      }
    };
    static Max(i1, i2) {
      if ((i2).isLessThanOrEqualTo(i1)) {
        return i1;
      } else {
        return i2;
      }
    };
    static Min(i1, i2) {
      if ((i1).isLessThan(i2)) {
        return i1;
      } else {
        return i2;
      }
    };
    static NatToString(n) {
      let _0___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(10))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(Int.__default.DigitToString(n)), _0___accumulator);
        } else {
          _0___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(Int.__default.DigitToString((n).mod(new BigNumber(10)))), _0___accumulator);
          let _in0 = _dafny.EuclideanDivision(n, new BigNumber(10));
          n = _in0;
          continue TAIL_CALL_START;
        }
      }
    };
    static IntToString(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.UnicodeFromString("0");
      } else if ((_dafny.ZERO).isLessThan(n)) {
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("+"), Int.__default.NatToString(n));
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("-"), Int.__default.NatToString((_dafny.ZERO).minus(n)));
      }
    };
    static DigitToString(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      } else if ((n).isEqualTo(_dafny.ONE)) {
        return new _dafny.CodePoint('1'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(2))) {
        return new _dafny.CodePoint('2'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(3))) {
        return new _dafny.CodePoint('3'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(4))) {
        return new _dafny.CodePoint('4'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(5))) {
        return new _dafny.CodePoint('5'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(6))) {
        return new _dafny.CodePoint('6'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(7))) {
        return new _dafny.CodePoint('7'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(8))) {
        return new _dafny.CodePoint('8'.codePointAt(0));
      } else {
        return new _dafny.CodePoint('9'.codePointAt(0));
      }
    };
    static get TWO__8() {
      return new BigNumber(256);
    };
    static get MAX__U8() {
      return (Int.__default.TWO__8).minus(_dafny.ONE);
    };
    static get TWO__16() {
      return new BigNumber(65536);
    };
    static get MAX__U16() {
      return (Int.__default.TWO__16).minus(_dafny.ONE);
    };
    static get TWO__32() {
      return new BigNumber(4294967296);
    };
    static get MAX__U32() {
      return (Int.__default.TWO__32).minus(_dafny.ONE);
    };
    static get TWO__64() {
      return new BigNumber("18446744073709551616");
    };
    static get MAX__U64() {
      return (Int.__default.TWO__64).minus(_dafny.ONE);
    };
    static get TWO__128() {
      return new BigNumber("340282366920938463463374607431768211456");
    };
    static get MAX__U128() {
      return (Int.__default.TWO__128).minus(_dafny.ONE);
    };
    static get TWO__256() {
      return new BigNumber("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    };
    static get MAX__U256() {
      return (Int.__default.TWO__256).minus(_dafny.ONE);
    };
    static get TWO__4() {
      return new BigNumber(16);
    };
  };

  $module.u8 = class u8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.u16 = class u16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.u32 = class u32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.u64 = class u64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.u128 = class u128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.u256 = class u256 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module Int
let MiscTypes = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "MiscTypes._default";
    }
    _parentTraits() {
      return [];
    }
    static Zip(u, v) {
      return _dafny.Seq.Create(new BigNumber((u).length), ((_1_u, _2_v) => function (_3_i) {
        return _dafny.Tuple.of((_1_u)[_3_i], (_2_v)[_3_i]);
      })(u, v));
    };
    static UnZip(x) {
      let _4_x0 = _dafny.Seq.Create(new BigNumber((x).length), ((_5_x) => function (_6_i) {
        return ((_5_x)[_6_i])[0];
      })(x));
      let _7_x1 = _dafny.Seq.Create(new BigNumber((x).length), ((_8_x) => function (_9_i) {
        return ((_8_x)[_9_i])[1];
      })(x));
      return _dafny.Tuple.of(_4_x0, _7_x1);
    };
    static Filter(u, f) {
      let _10___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((u).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_10___accumulator, _dafny.Seq.of());
        } else if ((f)((u)[_dafny.ZERO])) {
          _10___accumulator = _dafny.Seq.Concat(_10___accumulator, _dafny.Seq.of((u)[_dafny.ZERO]));
          let _in1 = (u).slice(_dafny.ONE);
          let _in2 = f;
          u = _in1;
          f = _in2;
          continue TAIL_CALL_START;
        } else {
          let _in3 = (u).slice(_dafny.ONE);
          let _in4 = f;
          u = _in3;
          f = _in4;
          continue TAIL_CALL_START;
        }
      }
    };
    static Exists(xs, f) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return false;
        } else if ((f)((xs)[_dafny.ZERO])) {
          return true;
        } else {
          let _in5 = (xs).slice(_dafny.ONE);
          let _in6 = f;
          xs = _in5;
          f = _in6;
          continue TAIL_CALL_START;
        }
      }
    };
    static Map(t, f) {
      return _dafny.Seq.Create(new BigNumber((t).length), ((_11_f, _12_t) => function (_13_i) {
        return (_11_f)((_12_t)[_13_i]);
      })(f, t));
    };
    static Find(x, t) {
      return MiscTypes.__default.FindRec(x, t, _dafny.ZERO);
    };
    static FindRec(x, t, i) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((x).length)).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Option.create_None();
        } else if (_dafny.areEqual((x)[_dafny.ZERO], t)) {
          return MiscTypes.Option.create_Some(i);
        } else {
          let _in7 = (x).slice(_dafny.ONE);
          let _in8 = t;
          let _in9 = (i).plus(_dafny.ONE);
          x = _in7;
          t = _in8;
          i = _in9;
          continue TAIL_CALL_START;
        }
      }
    };
  };

  $module.Try = class Try {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Success(v) {
      let $dt = new Try(0);
      $dt.v = v;
      return $dt;
    }
    static create_Failure(msg) {
      let $dt = new Try(1);
      $dt.msg = msg;
      return $dt;
    }
    get is_Success() { return this.$tag === 0; }
    get is_Failure() { return this.$tag === 1; }
    get dtor_v() { return this.v; }
    get dtor_msg() { return this.msg; }
    toString() {
      if (this.$tag === 0) {
        return "MiscTypes.Try.Success" + "(" + _dafny.toString(this.v) + ")";
      } else if (this.$tag === 1) {
        return "MiscTypes.Try.Failure" + "(" + this.msg.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.v, other.v);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.msg, other.msg);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return MiscTypes.Try.create_Failure('');
    }
    static Rtd() {
      return class {
        static get Default() {
          return Try.Default();
        }
      };
    }
  }

  $module.Option = class Option {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_None() {
      let $dt = new Option(0);
      return $dt;
    }
    static create_Some(v) {
      let $dt = new Option(1);
      $dt.v = v;
      return $dt;
    }
    get is_None() { return this.$tag === 0; }
    get is_Some() { return this.$tag === 1; }
    get dtor_v() { return this.v; }
    toString() {
      if (this.$tag === 0) {
        return "MiscTypes.Option.None";
      } else if (this.$tag === 1) {
        return "MiscTypes.Option.Some" + "(" + _dafny.toString(this.v) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.v, other.v);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return MiscTypes.Option.create_None();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Option.Default();
        }
      };
    }
    Extract() {
      let _this = this;
      return (_this).dtor_v;
    };
  }

  $module.Either = class Either {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Left(l) {
      let $dt = new Either(0);
      $dt.l = l;
      return $dt;
    }
    static create_Right(r) {
      let $dt = new Either(1);
      $dt.r = r;
      return $dt;
    }
    get is_Left() { return this.$tag === 0; }
    get is_Right() { return this.$tag === 1; }
    get dtor_l() { return this.l; }
    get dtor_r() { return this.r; }
    toString() {
      if (this.$tag === 0) {
        return "MiscTypes.Either.Left" + "(" + _dafny.toString(this.l) + ")";
      } else if (this.$tag === 1) {
        return "MiscTypes.Either.Right" + "(" + _dafny.toString(this.r) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.l, other.l);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.r, other.r);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_T) {
      return MiscTypes.Either.create_Left(_default_T);
    }
    static Rtd(rtd$_T) {
      return class {
        static get Default() {
          return Either.Default(rtd$_T.Default);
        }
      };
    }
    Left() {
      let _this = this;
      return (_this).dtor_l;
    };
    Right() {
      let _this = this;
      return (_this).dtor_r;
    };
  }
  return $module;
})(); // end of module MiscTypes
let EVMConstants = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "EVMConstants._default";
    }
    _parentTraits() {
      return [];
    }
    static get STOP() {
      return 0;
    };
    static get ADD() {
      return 1;
    };
    static get MUL() {
      return 2;
    };
    static get SUB() {
      return 3;
    };
    static get DIV() {
      return 4;
    };
    static get SDIV() {
      return 5;
    };
    static get MOD() {
      return 6;
    };
    static get SMOD() {
      return 7;
    };
    static get ADDMOD() {
      return 8;
    };
    static get MULMOD() {
      return 9;
    };
    static get EXP() {
      return 10;
    };
    static get SIGNEXTEND() {
      return 11;
    };
    static get LT() {
      return 16;
    };
    static get GT() {
      return 17;
    };
    static get SLT() {
      return 18;
    };
    static get SGT() {
      return 19;
    };
    static get EQ() {
      return 20;
    };
    static get ISZERO() {
      return 21;
    };
    static get AND() {
      return 22;
    };
    static get OR() {
      return 23;
    };
    static get XOR() {
      return 24;
    };
    static get NOT() {
      return 25;
    };
    static get BYTE() {
      return 26;
    };
    static get SHL() {
      return 27;
    };
    static get SHR() {
      return 28;
    };
    static get SAR() {
      return 29;
    };
    static get KECCAK256() {
      return 32;
    };
    static get ADDRESS() {
      return 48;
    };
    static get BALANCE() {
      return 49;
    };
    static get ORIGIN() {
      return 50;
    };
    static get CALLER() {
      return 51;
    };
    static get CALLVALUE() {
      return 52;
    };
    static get CALLDATALOAD() {
      return 53;
    };
    static get CALLDATASIZE() {
      return 54;
    };
    static get CALLDATACOPY() {
      return 55;
    };
    static get CODESIZE() {
      return 56;
    };
    static get CODECOPY() {
      return 57;
    };
    static get GASPRICE() {
      return 58;
    };
    static get EXTCODESIZE() {
      return 59;
    };
    static get EXTCODECOPY() {
      return 60;
    };
    static get RETURNDATASIZE() {
      return 61;
    };
    static get RETURNDATACOPY() {
      return 62;
    };
    static get EXTCODEHASH() {
      return 63;
    };
    static get BLOCKHASH() {
      return 64;
    };
    static get COINBASE() {
      return 65;
    };
    static get TIMESTAMP() {
      return 66;
    };
    static get NUMBER() {
      return 67;
    };
    static get DIFFICULTY() {
      return 68;
    };
    static get GASLIMIT() {
      return 69;
    };
    static get CHAINID() {
      return 70;
    };
    static get SELFBALANCE() {
      return 71;
    };
    static get BASEFEE() {
      return 72;
    };
    static get POP() {
      return 80;
    };
    static get MLOAD() {
      return 81;
    };
    static get MSTORE() {
      return 82;
    };
    static get MSTORE8() {
      return 83;
    };
    static get SLOAD() {
      return 84;
    };
    static get SSTORE() {
      return 85;
    };
    static get JUMP() {
      return 86;
    };
    static get JUMPI() {
      return 87;
    };
    static get PC() {
      return 88;
    };
    static get MSIZE() {
      return 89;
    };
    static get GAS() {
      return 90;
    };
    static get JUMPDEST() {
      return 91;
    };
    static get RJUMP() {
      return 92;
    };
    static get RJUMPI() {
      return 93;
    };
    static get RJUMPV() {
      return 94;
    };
    static get PUSH0() {
      return 95;
    };
    static get PUSH1() {
      return 96;
    };
    static get PUSH2() {
      return 97;
    };
    static get PUSH3() {
      return 98;
    };
    static get PUSH4() {
      return 99;
    };
    static get PUSH5() {
      return 100;
    };
    static get PUSH6() {
      return 101;
    };
    static get PUSH7() {
      return 102;
    };
    static get PUSH8() {
      return 103;
    };
    static get PUSH9() {
      return 104;
    };
    static get PUSH10() {
      return 105;
    };
    static get PUSH11() {
      return 106;
    };
    static get PUSH12() {
      return 107;
    };
    static get PUSH13() {
      return 108;
    };
    static get PUSH14() {
      return 109;
    };
    static get PUSH15() {
      return 110;
    };
    static get PUSH16() {
      return 111;
    };
    static get PUSH17() {
      return 112;
    };
    static get PUSH18() {
      return 113;
    };
    static get PUSH19() {
      return 114;
    };
    static get PUSH20() {
      return 115;
    };
    static get PUSH21() {
      return 116;
    };
    static get PUSH22() {
      return 117;
    };
    static get PUSH23() {
      return 118;
    };
    static get PUSH24() {
      return 119;
    };
    static get PUSH25() {
      return 120;
    };
    static get PUSH26() {
      return 121;
    };
    static get PUSH27() {
      return 122;
    };
    static get PUSH28() {
      return 123;
    };
    static get PUSH29() {
      return 124;
    };
    static get PUSH30() {
      return 125;
    };
    static get PUSH31() {
      return 126;
    };
    static get PUSH32() {
      return 127;
    };
    static get DUP1() {
      return 128;
    };
    static get DUP2() {
      return 129;
    };
    static get DUP3() {
      return 130;
    };
    static get DUP4() {
      return 131;
    };
    static get DUP5() {
      return 132;
    };
    static get DUP6() {
      return 133;
    };
    static get DUP7() {
      return 134;
    };
    static get DUP8() {
      return 135;
    };
    static get DUP9() {
      return 136;
    };
    static get DUP10() {
      return 137;
    };
    static get DUP11() {
      return 138;
    };
    static get DUP12() {
      return 139;
    };
    static get DUP13() {
      return 140;
    };
    static get DUP14() {
      return 141;
    };
    static get DUP15() {
      return 142;
    };
    static get DUP16() {
      return 143;
    };
    static get SWAP1() {
      return 144;
    };
    static get SWAP2() {
      return 145;
    };
    static get SWAP3() {
      return 146;
    };
    static get SWAP4() {
      return 147;
    };
    static get SWAP5() {
      return 148;
    };
    static get SWAP6() {
      return 149;
    };
    static get SWAP7() {
      return 150;
    };
    static get SWAP8() {
      return 151;
    };
    static get SWAP9() {
      return 152;
    };
    static get SWAP10() {
      return 153;
    };
    static get SWAP11() {
      return 154;
    };
    static get SWAP12() {
      return 155;
    };
    static get SWAP13() {
      return 156;
    };
    static get SWAP14() {
      return 157;
    };
    static get SWAP15() {
      return 158;
    };
    static get SWAP16() {
      return 159;
    };
    static get LOG0() {
      return 160;
    };
    static get LOG1() {
      return 161;
    };
    static get LOG2() {
      return 162;
    };
    static get LOG3() {
      return 163;
    };
    static get LOG4() {
      return 164;
    };
    static get EOF() {
      return 239;
    };
    static get CREATE() {
      return 240;
    };
    static get CALL() {
      return 241;
    };
    static get CALLCODE() {
      return 242;
    };
    static get RETURN() {
      return 243;
    };
    static get DELEGATECALL() {
      return 244;
    };
    static get CREATE2() {
      return 245;
    };
    static get STATICCALL() {
      return 250;
    };
    static get REVERT() {
      return 253;
    };
    static get INVALID() {
      return 254;
    };
    static get SELFDESTRUCT() {
      return 255;
    };
  };
  return $module;
})(); // end of module EVMConstants
let EVMOpcodes = (function() {
  let $module = {};


  $module.ValidOpcode = class ValidOpcode {
    constructor () {
    }
    static get Witness() {
      return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("STOP"), EVMConstants.__default.STOP, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO);
    }
    static get Default() {
      return EVMOpcodes.ValidOpcode.Witness;
    }
  };

  $module.Opcode = class Opcode {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ArithOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(0);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_CompOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(1);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_BitwiseOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(2);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_KeccakOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(3);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_EnvOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(4);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_MemOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(5);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_StorageOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(6);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_JumpOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(7);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_RunOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(8);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_StackOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(9);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_LogOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(10);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    static create_SysOp(name, opcode, minCapacity, minOperands, pushes, pops) {
      let $dt = new Opcode(11);
      $dt.name = name;
      $dt.opcode = opcode;
      $dt.minCapacity = minCapacity;
      $dt.minOperands = minOperands;
      $dt.pushes = pushes;
      $dt.pops = pops;
      return $dt;
    }
    get is_ArithOp() { return this.$tag === 0; }
    get is_CompOp() { return this.$tag === 1; }
    get is_BitwiseOp() { return this.$tag === 2; }
    get is_KeccakOp() { return this.$tag === 3; }
    get is_EnvOp() { return this.$tag === 4; }
    get is_MemOp() { return this.$tag === 5; }
    get is_StorageOp() { return this.$tag === 6; }
    get is_JumpOp() { return this.$tag === 7; }
    get is_RunOp() { return this.$tag === 8; }
    get is_StackOp() { return this.$tag === 9; }
    get is_LogOp() { return this.$tag === 10; }
    get is_SysOp() { return this.$tag === 11; }
    get dtor_name() { return this.name; }
    get dtor_opcode() { return this.opcode; }
    get dtor_minCapacity() { return this.minCapacity; }
    get dtor_minOperands() { return this.minOperands; }
    get dtor_pushes() { return this.pushes; }
    get dtor_pops() { return this.pops; }
    toString() {
      if (this.$tag === 0) {
        return "EVMOpcodes.Opcode.ArithOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 1) {
        return "EVMOpcodes.Opcode.CompOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 2) {
        return "EVMOpcodes.Opcode.BitwiseOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 3) {
        return "EVMOpcodes.Opcode.KeccakOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 4) {
        return "EVMOpcodes.Opcode.EnvOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 5) {
        return "EVMOpcodes.Opcode.MemOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 6) {
        return "EVMOpcodes.Opcode.StorageOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 7) {
        return "EVMOpcodes.Opcode.JumpOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 8) {
        return "EVMOpcodes.Opcode.RunOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 9) {
        return "EVMOpcodes.Opcode.StackOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 10) {
        return "EVMOpcodes.Opcode.LogOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else if (this.$tag === 11) {
        return "EVMOpcodes.Opcode.SysOp" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.opcode) + ", " + _dafny.toString(this.minCapacity) + ", " + _dafny.toString(this.minOperands) + ", " + _dafny.toString(this.pushes) + ", " + _dafny.toString(this.pops) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 5) {
        return other.$tag === 5 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 6) {
        return other.$tag === 6 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 7) {
        return other.$tag === 7 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 8) {
        return other.$tag === 8 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 9) {
        return other.$tag === 9 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 10) {
        return other.$tag === 10 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else if (this.$tag === 11) {
        return other.$tag === 11 && _dafny.areEqual(this.name, other.name) && this.opcode === other.opcode && _dafny.areEqual(this.minCapacity, other.minCapacity) && _dafny.areEqual(this.minOperands, other.minOperands) && _dafny.areEqual(this.pushes, other.pushes) && _dafny.areEqual(this.pops, other.pops);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return EVMOpcodes.Opcode.create_ArithOp('', 0, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Opcode.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      let _source0 = _this;
      if (_source0.is_ArithOp) {
        let _14___mcc_h0 = (_source0).name;
        let _15___mcc_h1 = (_source0).opcode;
        let _16___mcc_h2 = (_source0).minCapacity;
        let _17___mcc_h3 = (_source0).minOperands;
        let _18___mcc_h4 = (_source0).pushes;
        let _19___mcc_h5 = (_source0).pops;
        return ((((EVMConstants.__default.ADD) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SIGNEXTEND))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source0.is_CompOp) {
        let _20___mcc_h6 = (_source0).name;
        let _21___mcc_h7 = (_source0).opcode;
        let _22___mcc_h8 = (_source0).minCapacity;
        let _23___mcc_h9 = (_source0).minOperands;
        let _24___mcc_h10 = (_source0).pushes;
        let _25___mcc_h11 = (_source0).pops;
        return (((EVMConstants.__default.LT) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.ISZERO))) && (((_this).dtor_pushes).isLessThanOrEqualTo((_this).dtor_pops));
      } else if (_source0.is_BitwiseOp) {
        let _26___mcc_h12 = (_source0).name;
        let _27___mcc_h13 = (_source0).opcode;
        let _28___mcc_h14 = (_source0).minCapacity;
        let _29___mcc_h15 = (_source0).minOperands;
        let _30___mcc_h16 = (_source0).pushes;
        let _31___mcc_h17 = (_source0).pops;
        return (((EVMConstants.__default.AND) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SAR))) && (((_this).dtor_pushes).isLessThanOrEqualTo((_this).dtor_pops));
      } else if (_source0.is_KeccakOp) {
        let _32___mcc_h18 = (_source0).name;
        let _33___mcc_h19 = (_source0).opcode;
        let _34___mcc_h20 = (_source0).minCapacity;
        let _35___mcc_h21 = (_source0).minOperands;
        let _36___mcc_h22 = (_source0).pushes;
        let _37___mcc_h23 = (_source0).pops;
        return ((((_this).dtor_opcode) === (EVMConstants.__default.KECCAK256)) && (((_this).dtor_pops).isEqualTo(new BigNumber(2)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source0.is_EnvOp) {
        let _38___mcc_h24 = (_source0).name;
        let _39___mcc_h25 = (_source0).opcode;
        let _40___mcc_h26 = (_source0).minCapacity;
        let _41___mcc_h27 = (_source0).minOperands;
        let _42___mcc_h28 = (_source0).pushes;
        let _43___mcc_h29 = (_source0).pops;
        return (((EVMConstants.__default.ADDRESS) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.BASEFEE))) && (((((((_this).dtor_pushes).isEqualTo(_dafny.ONE)) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ONE)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ZERO)) && (((_this).dtor_pops).isEqualTo(new BigNumber(3))))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ZERO)) && (((_this).dtor_pops).isEqualTo(new BigNumber(4)))));
      } else if (_source0.is_MemOp) {
        let _44___mcc_h30 = (_source0).name;
        let _45___mcc_h31 = (_source0).opcode;
        let _46___mcc_h32 = (_source0).minCapacity;
        let _47___mcc_h33 = (_source0).minOperands;
        let _48___mcc_h34 = (_source0).pushes;
        let _49___mcc_h35 = (_source0).pops;
        return ((((_this).dtor_opcode) === (EVMConstants.__default.MLOAD)) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || (((((EVMConstants.__default.MSTORE) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.MSTORE8))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2))));
      } else if (_source0.is_StorageOp) {
        let _50___mcc_h36 = (_source0).name;
        let _51___mcc_h37 = (_source0).opcode;
        let _52___mcc_h38 = (_source0).minCapacity;
        let _53___mcc_h39 = (_source0).minOperands;
        let _54___mcc_h40 = (_source0).pushes;
        let _55___mcc_h41 = (_source0).pops;
        return (((EVMConstants.__default.SLOAD) === ((_this).dtor_opcode)) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || (((((_this).dtor_opcode) === (EVMConstants.__default.SSTORE)) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2))));
      } else if (_source0.is_JumpOp) {
        let _56___mcc_h42 = (_source0).name;
        let _57___mcc_h43 = (_source0).opcode;
        let _58___mcc_h44 = (_source0).minCapacity;
        let _59___mcc_h45 = (_source0).minOperands;
        let _60___mcc_h46 = (_source0).pushes;
        let _61___mcc_h47 = (_source0).pops;
        return ((((EVMConstants.__default.JUMP) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.JUMPI))) || (((EVMConstants.__default.JUMPDEST) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.RJUMPV)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO));
      } else if (_source0.is_RunOp) {
        let _62___mcc_h48 = (_source0).name;
        let _63___mcc_h49 = (_source0).opcode;
        let _64___mcc_h50 = (_source0).minCapacity;
        let _65___mcc_h51 = (_source0).minOperands;
        let _66___mcc_h52 = (_source0).pushes;
        let _67___mcc_h53 = (_source0).pops;
        return ((((EVMConstants.__default.PC) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.GAS))) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source0.is_StackOp) {
        let _68___mcc_h54 = (_source0).name;
        let _69___mcc_h55 = (_source0).opcode;
        let _70___mcc_h56 = (_source0).minCapacity;
        let _71___mcc_h57 = (_source0).minOperands;
        let _72___mcc_h58 = (_source0).pushes;
        let _73___mcc_h59 = (_source0).pops;
        return ((((((_this).dtor_opcode) === (EVMConstants.__default.POP)) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(_dafny.ONE))) || (((((EVMConstants.__default.PUSH0) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.DUP16))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE))) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO)))) || ((((EVMConstants.__default.SWAP1) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SWAP16))) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))));
      } else if (_source0.is_LogOp) {
        let _74___mcc_h60 = (_source0).name;
        let _75___mcc_h61 = (_source0).opcode;
        let _76___mcc_h62 = (_source0).minCapacity;
        let _77___mcc_h63 = (_source0).minOperands;
        let _78___mcc_h64 = (_source0).pushes;
        let _79___mcc_h65 = (_source0).pops;
        return ((((EVMConstants.__default.LOG0) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.LOG4))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo((new BigNumber(((_this).dtor_opcode) - (EVMConstants.__default.LOG0))).plus(new BigNumber(2))));
      } else {
        let _80___mcc_h66 = (_source0).name;
        let _81___mcc_h67 = (_source0).opcode;
        let _82___mcc_h68 = (_source0).minCapacity;
        let _83___mcc_h69 = (_source0).minOperands;
        let _84___mcc_h70 = (_source0).pushes;
        let _85___mcc_h71 = (_source0).pops;
        return (((((_this).dtor_opcode) === (EVMConstants.__default.STOP)) || (((_this).dtor_opcode) === (EVMConstants.__default.EOF))) || (((EVMConstants.__default.CREATE) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SELFDESTRUCT)))) && (((_this).dtor_pushes).isLessThanOrEqualTo(_dafny.ONE));
      }
    };
    Args() {
      let _this = this;
      if (((EVMConstants.__default.PUSH1) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.PUSH32))) {
        return new BigNumber(((_this).dtor_opcode) - (EVMConstants.__default.PUSH0));
      } else {
        return _dafny.ZERO;
      }
    };
    IsTerminal() {
      let _this = this;
      if (((_this).dtor_opcode) === (0)) {
        return true;
      } else if (((_this).dtor_opcode) === (86)) {
        return true;
      } else if (((_this).dtor_opcode) === (87)) {
        return true;
      } else if (((_this).dtor_opcode) === (92)) {
        return true;
      } else if (((_this).dtor_opcode) === (93)) {
        return true;
      } else if (((_this).dtor_opcode) === (94)) {
        return true;
      } else if (((_this).dtor_opcode) === (243)) {
        return true;
      } else if (((_this).dtor_opcode) === (253)) {
        return true;
      } else if (((_this).dtor_opcode) === (254)) {
        return true;
      } else {
        return false;
      }
    };
    IsJump() {
      let _this = this;
      if (((_this).dtor_opcode) === (86)) {
        return true;
      } else if (((_this).dtor_opcode) === (87)) {
        return true;
      } else {
        return false;
      }
    };
    IsJumpDest() {
      let _this = this;
      return ((_this).dtor_opcode) === (EVMConstants.__default.JUMPDEST);
    };
    Name() {
      let _this = this;
      return (_this).dtor_name;
    };
    StackEffect() {
      let _this = this;
      return ((_this).dtor_pushes).minus((_this).dtor_pops);
    };
    WeakestPreOperands(post) {
      let _this = this;
      return Int.__default.Max((_this).dtor_minOperands, (post).minus((_this).StackEffect()));
    };
    WeakestPreCapacity(post) {
      let _this = this;
      return Int.__default.Max((_this).dtor_minCapacity, (post).plus((_this).StackEffect()));
    };
  }
  return $module;
})(); // end of module EVMOpcodes
let OpcodeDecoder = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "OpcodeDecoder._default";
    }
    _parentTraits() {
      return [];
    }
    static Decode(op) {
      if ((op) === (0)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("STOP"), EVMConstants.__default.STOP, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (1)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("ADD"), EVMConstants.__default.ADD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (2)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("MUL"), EVMConstants.__default.MUL, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (3)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("SUB"), EVMConstants.__default.SUB, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (4)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("DIV"), EVMConstants.__default.DIV, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (5)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("SDIV"), EVMConstants.__default.SDIV, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (6)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("MOD"), EVMConstants.__default.MOD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (7)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("SMOD"), EVMConstants.__default.SMOD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (8)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("ADDMOD"), EVMConstants.__default.ADDMOD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (9)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("MULMOD"), EVMConstants.__default.MULMOD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (10)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("EXP"), EVMConstants.__default.EXP, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (11)) {
        return EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("SIGNEXTEND"), EVMConstants.__default.SIGNEXTEND, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (16)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("LT"), EVMConstants.__default.LT, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (17)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("GT"), EVMConstants.__default.GT, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (18)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("SLT"), EVMConstants.__default.SLT, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (19)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("SGT"), EVMConstants.__default.SGT, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (20)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("EQ"), EVMConstants.__default.EQ, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (21)) {
        return EVMOpcodes.Opcode.create_CompOp(_dafny.Seq.UnicodeFromString("ISZERO"), EVMConstants.__default.ISZERO, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (22)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("AND"), EVMConstants.__default.AND, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (23)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("OR"), EVMConstants.__default.OR, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (24)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("XOR"), EVMConstants.__default.XOR, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (25)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("NOT"), EVMConstants.__default.NOT, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (26)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("BYTE"), EVMConstants.__default.BYTE, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (27)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("SHL"), EVMConstants.__default.SHL, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (28)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("SHR"), EVMConstants.__default.SHR, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (29)) {
        return EVMOpcodes.Opcode.create_BitwiseOp(_dafny.Seq.UnicodeFromString("SAR"), EVMConstants.__default.SAR, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (32)) {
        return EVMOpcodes.Opcode.create_KeccakOp(_dafny.Seq.UnicodeFromString("KECCAK256"), EVMConstants.__default.KECCAK256, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2));
      } else if ((op) === (48)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("ADDRESS"), EVMConstants.__default.ADDRESS, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (49)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("BALANCE"), EVMConstants.__default.BALANCE, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (50)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("ORIGIN"), EVMConstants.__default.ORIGIN, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (51)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CALLER"), EVMConstants.__default.CALLER, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (52)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CALLVALUE"), EVMConstants.__default.CALLVALUE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (53)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CALLDATALOAD"), EVMConstants.__default.CALLDATALOAD, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (54)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CALLDATASIZE"), EVMConstants.__default.CALLDATASIZE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (55)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CALLDATACOPY"), EVMConstants.__default.CALLDATACOPY, _dafny.ZERO, new BigNumber(3), _dafny.ZERO, new BigNumber(3));
      } else if ((op) === (56)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CODESIZE"), EVMConstants.__default.CODESIZE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (57)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CODECOPY"), EVMConstants.__default.CODECOPY, _dafny.ZERO, new BigNumber(3), _dafny.ZERO, new BigNumber(3));
      } else if ((op) === (58)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("GASPRICE"), EVMConstants.__default.GASPRICE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (59)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("EXTCODESIZE"), EVMConstants.__default.EXTCODESIZE, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (60)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("EXTCODECOPY"), EVMConstants.__default.EXTCODECOPY, _dafny.ZERO, new BigNumber(4), _dafny.ZERO, new BigNumber(4));
      } else if ((op) === (61)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("RETURNDATASIZE"), EVMConstants.__default.RETURNDATASIZE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (62)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("RETURNDATACOPY"), EVMConstants.__default.RETURNDATACOPY, _dafny.ZERO, new BigNumber(3), _dafny.ZERO, new BigNumber(3));
      } else if ((op) === (63)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("EXTCODEHASH"), EVMConstants.__default.EXTCODEHASH, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (64)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("BLOCKHASH"), EVMConstants.__default.BLOCKHASH, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (65)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("COINBASE"), EVMConstants.__default.COINBASE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (66)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("TIMESTAMP"), EVMConstants.__default.TIMESTAMP, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (67)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("NUMBER"), EVMConstants.__default.NUMBER, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (68)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("DIFFICULTY"), EVMConstants.__default.DIFFICULTY, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (69)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("GASLIMIT"), EVMConstants.__default.GASLIMIT, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (70)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("CHAINID"), EVMConstants.__default.CHAINID, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (71)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("SELFBALANCE"), EVMConstants.__default.SELFBALANCE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (72)) {
        return EVMOpcodes.Opcode.create_EnvOp(_dafny.Seq.UnicodeFromString("BASEFEE"), EVMConstants.__default.BASEFEE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (80)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("POP"), EVMConstants.__default.POP, _dafny.ZERO, _dafny.ONE, _dafny.ZERO, _dafny.ONE);
      } else if ((op) === (81)) {
        return EVMOpcodes.Opcode.create_MemOp(_dafny.Seq.UnicodeFromString("MLOAD"), EVMConstants.__default.MLOAD, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (82)) {
        return EVMOpcodes.Opcode.create_MemOp(_dafny.Seq.UnicodeFromString("MSTORE"), EVMConstants.__default.MSTORE, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (83)) {
        return EVMOpcodes.Opcode.create_MemOp(_dafny.Seq.UnicodeFromString("MSTORE8"), EVMConstants.__default.MSTORE8, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (84)) {
        return EVMOpcodes.Opcode.create_StorageOp(_dafny.Seq.UnicodeFromString("SLOAD"), EVMConstants.__default.SLOAD, _dafny.ZERO, _dafny.ONE, _dafny.ONE, _dafny.ONE);
      } else if ((op) === (85)) {
        return EVMOpcodes.Opcode.create_StorageOp(_dafny.Seq.UnicodeFromString("SSTORE"), EVMConstants.__default.SSTORE, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (86)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("JUMP"), EVMConstants.__default.JUMP, _dafny.ZERO, _dafny.ONE, _dafny.ZERO, _dafny.ONE);
      } else if ((op) === (87)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("JUMPI"), EVMConstants.__default.JUMPI, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (92)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("RJUMP"), EVMConstants.__default.RJUMP, _dafny.ZERO, _dafny.ONE, _dafny.ZERO, _dafny.ONE);
      } else if ((op) === (93)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("RJUMPI"), EVMConstants.__default.RJUMPI, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (94)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("RJUMPV"), EVMConstants.__default.RJUMPV, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, new BigNumber(2));
      } else if ((op) === (88)) {
        return EVMOpcodes.Opcode.create_RunOp(_dafny.Seq.UnicodeFromString("PC"), EVMConstants.__default.PC, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (89)) {
        return EVMOpcodes.Opcode.create_RunOp(_dafny.Seq.UnicodeFromString("MSIZE"), EVMConstants.__default.MSIZE, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (90)) {
        return EVMOpcodes.Opcode.create_RunOp(_dafny.Seq.UnicodeFromString("GAS"), EVMConstants.__default.GAS, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (91)) {
        return EVMOpcodes.Opcode.create_JumpOp(_dafny.Seq.UnicodeFromString("JUMPDEST"), EVMConstants.__default.JUMPDEST, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (95)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH0"), EVMConstants.__default.PUSH0, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (96)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH1"), EVMConstants.__default.PUSH1, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (97)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH2"), EVMConstants.__default.PUSH2, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (98)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH3"), EVMConstants.__default.PUSH3, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (99)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH4"), EVMConstants.__default.PUSH4, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (100)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH5"), EVMConstants.__default.PUSH5, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (101)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH6"), EVMConstants.__default.PUSH6, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (102)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH7"), EVMConstants.__default.PUSH7, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (103)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH8"), EVMConstants.__default.PUSH8, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (104)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH9"), EVMConstants.__default.PUSH9, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (105)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH10"), EVMConstants.__default.PUSH10, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (106)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH11"), EVMConstants.__default.PUSH11, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (107)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH12"), EVMConstants.__default.PUSH12, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (108)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH13"), EVMConstants.__default.PUSH13, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (109)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH14"), EVMConstants.__default.PUSH14, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (110)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH15"), EVMConstants.__default.PUSH15, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (111)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH16"), EVMConstants.__default.PUSH16, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (112)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH17"), EVMConstants.__default.PUSH17, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (113)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH18"), EVMConstants.__default.PUSH18, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (114)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH19"), EVMConstants.__default.PUSH19, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (115)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH20"), EVMConstants.__default.PUSH20, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (116)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH21"), EVMConstants.__default.PUSH21, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (117)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH22"), EVMConstants.__default.PUSH22, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (118)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH23"), EVMConstants.__default.PUSH23, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (119)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH24"), EVMConstants.__default.PUSH24, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (120)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH25"), EVMConstants.__default.PUSH25, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (121)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH26"), EVMConstants.__default.PUSH26, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (122)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH27"), EVMConstants.__default.PUSH27, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (123)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH28"), EVMConstants.__default.PUSH28, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (124)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH29"), EVMConstants.__default.PUSH29, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (125)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH30"), EVMConstants.__default.PUSH30, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (126)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH31"), EVMConstants.__default.PUSH31, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (127)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("PUSH32"), EVMConstants.__default.PUSH32, _dafny.ONE, _dafny.ZERO, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (128)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP1"), EVMConstants.__default.DUP1, _dafny.ONE, _dafny.ONE, _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (129)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP2"), EVMConstants.__default.DUP2, _dafny.ONE, new BigNumber(2), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (130)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP3"), EVMConstants.__default.DUP3, _dafny.ONE, new BigNumber(3), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (131)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP4"), EVMConstants.__default.DUP4, _dafny.ONE, new BigNumber(4), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (132)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP5"), EVMConstants.__default.DUP5, _dafny.ONE, new BigNumber(5), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (133)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP6"), EVMConstants.__default.DUP6, _dafny.ONE, new BigNumber(6), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (134)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP7"), EVMConstants.__default.DUP7, _dafny.ONE, new BigNumber(7), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (135)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP8"), EVMConstants.__default.DUP8, _dafny.ONE, new BigNumber(8), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (136)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP9"), EVMConstants.__default.DUP9, _dafny.ONE, new BigNumber(9), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (137)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP10"), EVMConstants.__default.DUP10, _dafny.ONE, new BigNumber(10), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (138)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP11"), EVMConstants.__default.DUP11, _dafny.ONE, new BigNumber(11), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (139)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP12"), EVMConstants.__default.DUP12, _dafny.ONE, new BigNumber(12), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (140)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP13"), EVMConstants.__default.DUP13, _dafny.ONE, new BigNumber(13), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (141)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP14"), EVMConstants.__default.DUP14, _dafny.ONE, new BigNumber(14), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (142)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP15"), EVMConstants.__default.DUP15, _dafny.ONE, new BigNumber(15), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (143)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("DUP16"), EVMConstants.__default.DUP16, _dafny.ONE, new BigNumber(16), _dafny.ONE, _dafny.ZERO);
      } else if ((op) === (144)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP1"), EVMConstants.__default.SWAP1, _dafny.ZERO, (_dafny.ONE).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (145)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP2"), EVMConstants.__default.SWAP2, _dafny.ZERO, (new BigNumber(2)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (146)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP3"), EVMConstants.__default.SWAP3, _dafny.ZERO, (new BigNumber(3)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (147)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP4"), EVMConstants.__default.SWAP4, _dafny.ZERO, (new BigNumber(4)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (148)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP5"), EVMConstants.__default.SWAP5, _dafny.ZERO, (new BigNumber(5)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (149)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP6"), EVMConstants.__default.SWAP6, _dafny.ZERO, (new BigNumber(6)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (150)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP7"), EVMConstants.__default.SWAP7, _dafny.ZERO, (new BigNumber(7)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (151)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP8"), EVMConstants.__default.SWAP8, _dafny.ZERO, (new BigNumber(8)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (152)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP9"), EVMConstants.__default.SWAP9, _dafny.ZERO, (new BigNumber(9)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (153)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP10"), EVMConstants.__default.SWAP10, _dafny.ZERO, (new BigNumber(10)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (154)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP11"), EVMConstants.__default.SWAP11, _dafny.ZERO, (new BigNumber(11)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (155)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP12"), EVMConstants.__default.SWAP12, _dafny.ZERO, (new BigNumber(12)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (156)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP13"), EVMConstants.__default.SWAP13, _dafny.ZERO, (new BigNumber(13)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (157)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP14"), EVMConstants.__default.SWAP14, _dafny.ZERO, (new BigNumber(14)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (158)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP15"), EVMConstants.__default.SWAP15, _dafny.ZERO, (new BigNumber(15)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (159)) {
        return EVMOpcodes.Opcode.create_StackOp(_dafny.Seq.UnicodeFromString("SWAP16"), EVMConstants.__default.SWAP16, _dafny.ZERO, (new BigNumber(16)).plus(_dafny.ONE), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (160)) {
        return EVMOpcodes.Opcode.create_LogOp(_dafny.Seq.UnicodeFromString("LOG0"), EVMConstants.__default.LOG0, _dafny.ZERO, (_dafny.ZERO).plus(new BigNumber(2)), _dafny.ZERO, (_dafny.ZERO).plus(new BigNumber(2)));
      } else if ((op) === (161)) {
        return EVMOpcodes.Opcode.create_LogOp(_dafny.Seq.UnicodeFromString("LOG1"), EVMConstants.__default.LOG1, _dafny.ZERO, (_dafny.ONE).plus(new BigNumber(2)), _dafny.ZERO, (_dafny.ONE).plus(new BigNumber(2)));
      } else if ((op) === (162)) {
        return EVMOpcodes.Opcode.create_LogOp(_dafny.Seq.UnicodeFromString("LOG2"), EVMConstants.__default.LOG2, _dafny.ZERO, (new BigNumber(2)).plus(new BigNumber(2)), _dafny.ZERO, (new BigNumber(2)).plus(new BigNumber(2)));
      } else if ((op) === (163)) {
        return EVMOpcodes.Opcode.create_LogOp(_dafny.Seq.UnicodeFromString("LOG3"), EVMConstants.__default.LOG3, _dafny.ZERO, (new BigNumber(3)).plus(new BigNumber(2)), _dafny.ZERO, (new BigNumber(3)).plus(new BigNumber(2)));
      } else if ((op) === (164)) {
        return EVMOpcodes.Opcode.create_LogOp(_dafny.Seq.UnicodeFromString("LOG4"), EVMConstants.__default.LOG4, _dafny.ZERO, (new BigNumber(4)).plus(new BigNumber(2)), _dafny.ZERO, (new BigNumber(4)).plus(new BigNumber(2)));
      } else if ((op) === (240)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("CREATE"), EVMConstants.__default.CREATE, _dafny.ONE, new BigNumber(3), _dafny.ONE, new BigNumber(3));
      } else if ((op) === (241)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("CALL"), EVMConstants.__default.CALL, _dafny.ONE, new BigNumber(7), _dafny.ONE, new BigNumber(7));
      } else if ((op) === (242)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("CALLCODE"), EVMConstants.__default.CALLCODE, _dafny.ONE, new BigNumber(7), _dafny.ONE, new BigNumber(7));
      } else if ((op) === (243)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("RETURN"), EVMConstants.__default.RETURN, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (244)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("DELEGATECALL"), EVMConstants.__default.DELEGATECALL, _dafny.ONE, new BigNumber(6), _dafny.ONE, new BigNumber(6));
      } else if ((op) === (245)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("CREATE2"), EVMConstants.__default.CREATE2, _dafny.ONE, new BigNumber(4), _dafny.ONE, new BigNumber(4));
      } else if ((op) === (250)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("STATICCALL"), EVMConstants.__default.STATICCALL, _dafny.ONE, new BigNumber(6), _dafny.ONE, new BigNumber(6));
      } else if ((op) === (253)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("REVERT"), EVMConstants.__default.REVERT, _dafny.ZERO, new BigNumber(2), _dafny.ZERO, _dafny.ZERO);
      } else if ((op) === (255)) {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("SELFDESTRUCT"), EVMConstants.__default.SELFDESTRUCT, _dafny.ZERO, _dafny.ONE, _dafny.ZERO, _dafny.ONE);
      } else {
        return EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("INVALID"), EVMConstants.__default.INVALID, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO);
      }
    };
  };
  return $module;
})(); // end of module OpcodeDecoder
let Hex = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Hex._default";
    }
    _parentTraits() {
      return [];
    }
    static HexToU8(s) {
      let _source1 = _dafny.Tuple.of(Hex.__default.HexVal((s)[_dafny.ZERO]), Hex.__default.HexVal((s)[_dafny.ONE]));
      let _86___mcc_h0 = (_source1)[0];
      let _87___mcc_h1 = (_source1)[1];
      let _source2 = _86___mcc_h0;
      if (_source2.is_None) {
        let _source3 = _87___mcc_h1;
        if (_source3.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _88___mcc_h2 = (_source3).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _89___mcc_h4 = (_source2).v;
        let _source4 = _87___mcc_h1;
        if (_source4.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _90___mcc_h6 = (_source4).v;
          let _91_v2 = _90___mcc_h6;
          let _92_v1 = _89___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__4).multipliedBy(new BigNumber(_92_v1))).plus(new BigNumber(_91_v2))).toNumber());
        }
      }
    };
    static HexToU16(s) {
      let _source5 = _dafny.Tuple.of(Hex.__default.HexToU8((s).slice(0, new BigNumber(2))), Hex.__default.HexToU8((s).slice(new BigNumber(2))));
      let _93___mcc_h0 = (_source5)[0];
      let _94___mcc_h1 = (_source5)[1];
      let _source6 = _93___mcc_h0;
      if (_source6.is_None) {
        let _source7 = _94___mcc_h1;
        if (_source7.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _95___mcc_h2 = (_source7).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _96___mcc_h4 = (_source6).v;
        let _source8 = _94___mcc_h1;
        if (_source8.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _97___mcc_h6 = (_source8).v;
          let _98_v2 = _97___mcc_h6;
          let _99_v1 = _96___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__8).multipliedBy(new BigNumber(_99_v1))).plus(new BigNumber(_98_v2))).toNumber());
        }
      }
    };
    static HexToU32(s) {
      let _source9 = _dafny.Tuple.of(Hex.__default.HexToU16((s).slice(0, new BigNumber(4))), Hex.__default.HexToU16((s).slice(new BigNumber(4))));
      let _100___mcc_h0 = (_source9)[0];
      let _101___mcc_h1 = (_source9)[1];
      let _source10 = _100___mcc_h0;
      if (_source10.is_None) {
        let _source11 = _101___mcc_h1;
        if (_source11.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _102___mcc_h2 = (_source11).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _103___mcc_h4 = (_source10).v;
        let _source12 = _101___mcc_h1;
        if (_source12.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _104___mcc_h6 = (_source12).v;
          let _105_v2 = _104___mcc_h6;
          let _106_v1 = _103___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__16).multipliedBy(new BigNumber(_106_v1))).plus(new BigNumber(_105_v2))).toNumber());
        }
      }
    };
    static HexToU64(s) {
      let _source13 = _dafny.Tuple.of(Hex.__default.HexToU32((s).slice(0, new BigNumber(8))), Hex.__default.HexToU32((s).slice(new BigNumber(8))));
      let _107___mcc_h0 = (_source13)[0];
      let _108___mcc_h1 = (_source13)[1];
      let _source14 = _107___mcc_h0;
      if (_source14.is_None) {
        let _source15 = _108___mcc_h1;
        if (_source15.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _109___mcc_h2 = (_source15).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _110___mcc_h4 = (_source14).v;
        let _source16 = _108___mcc_h1;
        if (_source16.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _111___mcc_h6 = (_source16).v;
          let _112_v2 = _111___mcc_h6;
          let _113_v1 = _110___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__32).multipliedBy(new BigNumber(_113_v1))).plus(new BigNumber(_112_v2)));
        }
      }
    };
    static HexToU128(s) {
      let _source17 = _dafny.Tuple.of(Hex.__default.HexToU64((s).slice(0, new BigNumber(16))), Hex.__default.HexToU64((s).slice(new BigNumber(16))));
      let _114___mcc_h0 = (_source17)[0];
      let _115___mcc_h1 = (_source17)[1];
      let _source18 = _114___mcc_h0;
      if (_source18.is_None) {
        let _source19 = _115___mcc_h1;
        if (_source19.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _116___mcc_h2 = (_source19).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _117___mcc_h4 = (_source18).v;
        let _source20 = _115___mcc_h1;
        if (_source20.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _118___mcc_h6 = (_source20).v;
          let _119_v2 = _118___mcc_h6;
          let _120_v1 = _117___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__64).multipliedBy(_120_v1)).plus(_119_v2));
        }
      }
    };
    static HexToU256(s) {
      let _source21 = _dafny.Tuple.of(Hex.__default.HexToU128((s).slice(0, new BigNumber(32))), Hex.__default.HexToU128((s).slice(new BigNumber(32))));
      let _121___mcc_h0 = (_source21)[0];
      let _122___mcc_h1 = (_source21)[1];
      let _source22 = _121___mcc_h0;
      if (_source22.is_None) {
        let _source23 = _122___mcc_h1;
        if (_source23.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _123___mcc_h2 = (_source23).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _124___mcc_h4 = (_source22).v;
        let _source24 = _122___mcc_h1;
        if (_source24.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _125___mcc_h6 = (_source24).v;
          let _126_v2 = _125___mcc_h6;
          let _127_v1 = _124___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__128).multipliedBy(_127_v1)).plus(_126_v2));
        }
      }
    };
    static U8ToHex(n) {
      return _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex(_dafny.EuclideanDivision(new BigNumber(n), Int.__default.TWO__4))), _dafny.Seq.of(Hex.__default.DecToHex((new BigNumber(n)).mod(Int.__default.TWO__4))));
    };
    static U16ToHex(n) {
      return _dafny.Seq.Concat(Hex.__default.U8ToHex((_dafny.EuclideanDivision(new BigNumber(n), Int.__default.TWO__8)).toNumber()), Hex.__default.U8ToHex(((new BigNumber(n)).mod(Int.__default.TWO__8)).toNumber()));
    };
    static U32ToHex(n) {
      return _dafny.Seq.Concat(Hex.__default.U16ToHex((_dafny.EuclideanDivision(new BigNumber(n), Int.__default.TWO__16)).toNumber()), Hex.__default.U16ToHex(((new BigNumber(n)).mod(Int.__default.TWO__16)).toNumber()));
    };
    static U64ToHex(n) {
      return _dafny.Seq.Concat(Hex.__default.U32ToHex((_dafny.EuclideanDivision(n, Int.__default.TWO__32)).toNumber()), Hex.__default.U32ToHex(((n).mod(Int.__default.TWO__32)).toNumber()));
    };
    static U128ToHex(n) {
      return _dafny.Seq.Concat(Hex.__default.U64ToHex(_dafny.EuclideanDivision(n, Int.__default.TWO__64)), Hex.__default.U64ToHex((n).mod(Int.__default.TWO__64)));
    };
    static U256ToHex(n) {
      return _dafny.Seq.Concat(Hex.__default.U128ToHex(_dafny.EuclideanDivision(n, Int.__default.TWO__128)), Hex.__default.U128ToHex((n).mod(Int.__default.TWO__128)));
    };
    static NatToHex(n) {
      let _128___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(16))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex(n)), _128___accumulator);
        } else {
          _128___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex((n).mod(new BigNumber(16)))), _128___accumulator);
          let _in10 = _dafny.EuclideanDivision(n, new BigNumber(16));
          n = _in10;
          continue TAIL_CALL_START;
        }
      }
    };
    static HexVal(c) {
      if (_dafny.areEqual(c, new _dafny.CodePoint('0'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(0);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('1'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(1);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('2'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(2);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('3'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(3);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('4'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(4);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('5'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(5);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('6'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(6);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('7'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(7);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('8'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(8);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('9'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(9);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('a'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(10);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('A'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(10);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('b'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(11);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('B'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(11);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('c'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(12);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('C'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(12);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('d'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(13);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('D'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(13);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('e'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(14);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('E'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(14);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('f'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(15);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('F'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(15);
      } else {
        return MiscTypes.Option.create_None();
      }
    };
    static DecToHex(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      } else if ((n).isEqualTo(_dafny.ONE)) {
        return new _dafny.CodePoint('1'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(2))) {
        return new _dafny.CodePoint('2'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(3))) {
        return new _dafny.CodePoint('3'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(4))) {
        return new _dafny.CodePoint('4'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(5))) {
        return new _dafny.CodePoint('5'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(6))) {
        return new _dafny.CodePoint('6'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(7))) {
        return new _dafny.CodePoint('7'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(8))) {
        return new _dafny.CodePoint('8'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(9))) {
        return new _dafny.CodePoint('9'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(10))) {
        return new _dafny.CodePoint('a'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(11))) {
        return new _dafny.CodePoint('b'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(12))) {
        return new _dafny.CodePoint('c'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(13))) {
        return new _dafny.CodePoint('d'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(14))) {
        return new _dafny.CodePoint('e'.codePointAt(0));
      } else {
        return new _dafny.CodePoint('f'.codePointAt(0));
      }
    };
    static IsHex(c) {
      return ((((new _dafny.CodePoint('0'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('9'.codePointAt(0))))) || (((new _dafny.CodePoint('a'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('f'.codePointAt(0)))))) || (((new _dafny.CodePoint('A'.codePointAt(0))).isLessThanOrEqual(c)) && ((c).isLessThanOrEqual(new _dafny.CodePoint('F'.codePointAt(0)))));
    };
  };
  return $module;
})(); // end of module Hex
let StackElement = (function() {
  let $module = {};


  $module.StackElem = class StackElem {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Value(v) {
      let $dt = new StackElem(0);
      $dt.v = v;
      return $dt;
    }
    static create_Random(s) {
      let $dt = new StackElem(1);
      $dt.s = s;
      return $dt;
    }
    get is_Value() { return this.$tag === 0; }
    get is_Random() { return this.$tag === 1; }
    get dtor_v() { return this.v; }
    get dtor_s() { return this.s; }
    toString() {
      if (this.$tag === 0) {
        return "StackElement.StackElem.Value" + "(" + _dafny.toString(this.v) + ")";
      } else if (this.$tag === 1) {
        return "StackElement.StackElem.Random" + "(" + this.s.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.v, other.v);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.s, other.s);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return StackElement.StackElem.create_Value(_dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return StackElem.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      let _source25 = _this;
      if (_source25.is_Value) {
        let _129___mcc_h0 = (_source25).v;
        let _130_v = _129___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(Int.__default.NatToString(_130_v), _dafny.Seq.UnicodeFromString("(0x")), Hex.__default.NatToHex(_130_v)), _dafny.Seq.UnicodeFromString(")"));
      } else {
        let _131___mcc_h1 = (_source25).s;
        return _dafny.Seq.UnicodeFromString("?");
      }
    };
    Extract() {
      let _this = this;
      return (_this).dtor_v;
    };
  }
  return $module;
})(); // end of module StackElement
let WeakPre = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "WeakPre._default";
    }
    _parentTraits() {
      return [];
    }
    static Merge(c1, c2) {
      TAIL_CALL_START: while (true) {
        if (((c2).Size()).isEqualTo(_dafny.ZERO)) {
          return c1;
        } else if (((c2).Size()).isEqualTo(_dafny.ONE)) {
          if (_dafny.Seq.contains((c1).dtor_trackedPos, ((c2).dtor_trackedPos)[_dafny.ZERO])) {
            let _132_i = WeakPre.__default.FindVal(((c2).dtor_trackedPos)[_dafny.ZERO], (c1).dtor_trackedPos, _dafny.ZERO);
            if (_dafny.areEqual(((c1).dtor_trackedVals)[_132_i], ((c2).dtor_trackedVals)[_dafny.ZERO])) {
              return c1;
            } else {
              return WeakPre.Cond.create_StFalse();
            }
          } else {
            return WeakPre.Cond.create_StCond(_dafny.Seq.Concat((c1).dtor_trackedPos, _dafny.Seq.of(((c2).dtor_trackedPos)[_dafny.ZERO])), _dafny.Seq.Concat((c1).dtor_trackedVals, _dafny.Seq.of(((c2).dtor_trackedVals)[_dafny.ZERO])));
          }
        } else {
          if (_dafny.Seq.contains((c1).dtor_trackedPos, ((c2).dtor_trackedPos)[_dafny.ZERO])) {
            let _in11 = c1;
            let _in12 = WeakPre.Cond.create_StCond(((c2).dtor_trackedPos).slice(_dafny.ONE), ((c2).dtor_trackedVals).slice(_dafny.ONE));
            c1 = _in11;
            c2 = _in12;
            continue TAIL_CALL_START;
          } else {
            let _133_p = _dafny.Seq.Concat((c1).dtor_trackedPos, _dafny.Seq.of(((c2).dtor_trackedPos)[_dafny.ZERO]));
            let _134_v = _dafny.Seq.Concat((c1).dtor_trackedVals, _dafny.Seq.of(((c2).dtor_trackedVals)[_dafny.ZERO]));
            let _in13 = WeakPre.Cond.create_StCond(_133_p, _134_v);
            let _in14 = WeakPre.Cond.create_StCond(((c2).dtor_trackedPos).slice(_dafny.ONE), ((c2).dtor_trackedVals).slice(_dafny.ONE));
            c1 = _in13;
            c2 = _in14;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static FindVal(x, xs, index) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ONE)) {
          return index;
        } else if (_dafny.areEqual((xs)[index], x)) {
          return index;
        } else {
          let _in15 = x;
          let _in16 = xs;
          let _in17 = (index).plus(_dafny.ONE);
          x = _in15;
          xs = _in16;
          index = _in17;
          continue TAIL_CALL_START;
        }
      }
    };
  };

  $module.ValidCond = class ValidCond {
    constructor () {
    }
    static get Witness() {
      return WeakPre.Cond.create_StCond(_dafny.Seq.of(_dafny.ONE), _dafny.Seq.of(_dafny.ZERO));
    }
    static get Default() {
      return WeakPre.ValidCond.Witness;
    }
  };

  $module.Cond = class Cond {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_StTrue() {
      let $dt = new Cond(0);
      return $dt;
    }
    static create_StFalse() {
      let $dt = new Cond(1);
      return $dt;
    }
    static create_StCond(trackedPos, trackedVals) {
      let $dt = new Cond(2);
      $dt.trackedPos = trackedPos;
      $dt.trackedVals = trackedVals;
      return $dt;
    }
    get is_StTrue() { return this.$tag === 0; }
    get is_StFalse() { return this.$tag === 1; }
    get is_StCond() { return this.$tag === 2; }
    get dtor_trackedPos() { return this.trackedPos; }
    get dtor_trackedVals() { return this.trackedVals; }
    toString() {
      if (this.$tag === 0) {
        return "WeakPre.Cond.StTrue";
      } else if (this.$tag === 1) {
        return "WeakPre.Cond.StFalse";
      } else if (this.$tag === 2) {
        return "WeakPre.Cond.StCond" + "(" + _dafny.toString(this.trackedPos) + ", " + _dafny.toString(this.trackedVals) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.trackedPos, other.trackedPos) && _dafny.areEqual(this.trackedVals, other.trackedVals);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return WeakPre.Cond.create_StTrue();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Cond.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      return !((_this).is_StCond) || ((((new BigNumber(((_this).dtor_trackedPos).length)).isEqualTo(new BigNumber(((_this).dtor_trackedVals).length))) && ((_dafny.ZERO).isLessThan(new BigNumber(((_this).dtor_trackedVals).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((_this).dtor_trackedPos).length)), true, function (_forall_var_0) {
        let _135_k = _forall_var_0;
        return _dafny.Quantifier(_dafny.IntegerRange((_135_k).plus(_dafny.ONE), new BigNumber(((_this).dtor_trackedPos).length)), true, function (_forall_var_1) {
          let _136_k_k = _forall_var_1;
          return !((((_dafny.ZERO).isLessThanOrEqualTo(_135_k)) && ((_135_k).isLessThan(_136_k_k))) && ((_136_k_k).isLessThan(new BigNumber(((_this).dtor_trackedPos).length)))) || (!(((_this).dtor_trackedPos)[_135_k]).isEqualTo(((_this).dtor_trackedPos)[_136_k_k]));
        });
      })));
    };
    Size() {
      let _this = this;
      if ((_this).is_StCond) {
        return new BigNumber(((_this).dtor_trackedPos).length);
      } else {
        return _dafny.ZERO;
      }
    };
    And(c) {
      let _this = this;
      let _source26 = _dafny.Tuple.of(_this, c);
      let _137___mcc_h0 = (_source26)[0];
      let _138___mcc_h1 = (_source26)[1];
      let _source27 = _137___mcc_h0;
      if (_source27.is_StTrue) {
        let _source28 = _138___mcc_h1;
        if (_source28.is_StTrue) {
          let _139_cond = _138___mcc_h1;
          return _139_cond;
        } else if (_source28.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _140___mcc_h2 = (_source28).trackedPos;
          let _141___mcc_h3 = (_source28).trackedVals;
          let _142_cond = _138___mcc_h1;
          return _142_cond;
        }
      } else if (_source27.is_StFalse) {
        let _source29 = _138___mcc_h1;
        if (_source29.is_StTrue) {
          return WeakPre.Cond.create_StFalse();
        } else if (_source29.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _143___mcc_h8 = (_source29).trackedPos;
          let _144___mcc_h9 = (_source29).trackedVals;
          return WeakPre.Cond.create_StFalse();
        }
      } else {
        let _145___mcc_h14 = (_source27).trackedPos;
        let _146___mcc_h15 = (_source27).trackedVals;
        let _source30 = _138___mcc_h1;
        if (_source30.is_StTrue) {
          let _147_c1 = _137___mcc_h0;
          return _147_c1;
        } else if (_source30.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _148___mcc_h22 = (_source30).trackedPos;
          let _149___mcc_h23 = (_source30).trackedVals;
          let _150_c2 = _138___mcc_h1;
          let _151_c1 = _137___mcc_h0;
          return WeakPre.__default.Merge(_151_c1, _150_c2);
        }
      }
    };
    TrackedPos() {
      let _this = this;
      return (_this).dtor_trackedPos;
    };
    TrackedVals() {
      let _this = this;
      return (_this).dtor_trackedVals;
    };
    TrackedPosAt(i) {
      let _this = this;
      return ((_this).dtor_trackedPos)[i];
    };
    TrackedValAt(i) {
      let _this = this;
      return ((_this).dtor_trackedVals)[i];
    };
    Tail() {
      let _this = this;
      let _152_dt__update__tmp_h0 = _this;
      let _153_dt__update_htrackedVals_h0 = ((_this).dtor_trackedVals).slice(_dafny.ONE);
      let _154_dt__update_htrackedPos_h0 = ((_this).dtor_trackedPos).slice(_dafny.ONE);
      return WeakPre.Cond.create_StCond(_154_dt__update_htrackedPos_h0, _153_dt__update_htrackedVals_h0);
    };
    Add(pos, val) {
      let _this = this;
      return _this;
    };
    BuildStack(r, index) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((index).isEqualTo(new BigNumber(((_this).dtor_trackedPos).length))) {
          return r;
        } else if ((((_this).dtor_trackedPos)[index]).isLessThan(new BigNumber((r).length))) {
          let _in18 = _this;
          let _in19 = _dafny.Seq.update(r, ((_this).dtor_trackedPos)[index], StackElement.StackElem.create_Value(((_this).dtor_trackedVals)[index]));
          let _in20 = (index).plus(_dafny.ONE);
          _this = _in18;
          ;
          r = _in19;
          index = _in20;
          continue TAIL_CALL_START;
        } else {
          let _155_suf = _dafny.Seq.Create((((_this).dtor_trackedPos)[index]).minus(new BigNumber((r).length)), function (_156___v2) {
            return StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString(""));
          });
          let _in21 = _this;
          let _in22 = _dafny.Seq.Concat(_dafny.Seq.Concat(r, _155_suf), _dafny.Seq.of(StackElement.StackElem.create_Value(((_this).dtor_trackedVals)[index])));
          let _in23 = (index).plus(_dafny.ONE);
          _this = _in21;
          ;
          r = _in22;
          index = _in23;
          continue TAIL_CALL_START;
        }
      }
    };
  }
  return $module;
})(); // end of module WeakPre
let State = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "State._default";
    }
    _parentTraits() {
      return [];
    }
    static checkPos(s, pos, val) {
      if ((new BigNumber(((s).dtor_stack).length)).isLessThanOrEqualTo(pos)) {
        return false;
      } else {
        return _dafny.areEqual(((s).dtor_stack)[pos], StackElement.StackElem.create_Value(val));
      }
    };
    static StackToString(s) {
      let _157___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_157___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _157___accumulator = _dafny.Seq.Concat(_157___accumulator, _dafny.Seq.Concat(((s)[_dafny.ZERO]).ToString(), _dafny.Seq.UnicodeFromString(",")));
          let _in24 = (s).slice(_dafny.ONE);
          s = _in24;
          continue TAIL_CALL_START;
        }
      }
    };
    static BuildInitState(c, initpc) {
      let _158_s0 = State.__default.DEFAULT__VALIDSTATE;
      if ((c).is_StCond) {
        let _159_dt__update__tmp_h0 = _158_s0;
        let _160_dt__update_hpc_h0 = initpc;
        let _161_dt__update_hstack_h0 = (c).BuildStack(_dafny.Seq.of(), _dafny.ZERO);
        return State.AState.create_EState(_160_dt__update_hpc_h0, _161_dt__update_hstack_h0);
      } else {
        let _162_dt__update__tmp_h1 = _158_s0;
        let _163_dt__update_hpc_h1 = initpc;
        return State.AState.create_EState(_163_dt__update_hpc_h1, (_162_dt__update__tmp_h1).dtor_stack);
      }
    };
    static get DEFAULT__VALIDSTATE() {
      return State.AState.create_EState(_dafny.ZERO, _dafny.Seq.of());
    };
  };

  $module.ValidState = class ValidState {
    constructor () {
    }
    static get Witness() {
      return State.__default.DEFAULT__VALIDSTATE;
    }
    static get Default() {
      return State.ValidState.Witness;
    }
  };

  $module.AState = class AState {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_EState(pc, stack) {
      let $dt = new AState(0);
      $dt.pc = pc;
      $dt.stack = stack;
      return $dt;
    }
    static create_Error(msg) {
      let $dt = new AState(1);
      $dt.msg = msg;
      return $dt;
    }
    get is_EState() { return this.$tag === 0; }
    get is_Error() { return this.$tag === 1; }
    get dtor_pc() { return this.pc; }
    get dtor_stack() { return this.stack; }
    get dtor_msg() { return this.msg; }
    toString() {
      if (this.$tag === 0) {
        return "State.AState.EState" + "(" + _dafny.toString(this.pc) + ", " + _dafny.toString(this.stack) + ")";
      } else if (this.$tag === 1) {
        return "State.AState.Error" + "(" + this.msg.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.pc, other.pc) && _dafny.areEqual(this.stack, other.stack);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.msg, other.msg);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return State.AState.create_EState(_dafny.ZERO, _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return AState.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      let _source31 = _this;
      if (_source31.is_EState) {
        let _164___mcc_h0 = (_source31).pc;
        let _165___mcc_h1 = (_source31).stack;
        let _166_stack = _165___mcc_h1;
        let _167_pc = _164___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("(pc=0x"), Hex.__default.NatToHex(_167_pc)), _dafny.Seq.UnicodeFromString(" stack:[")), State.__default.StackToString(_166_stack)), _dafny.Seq.UnicodeFromString("])"));
      } else {
        let _168___mcc_h2 = (_source31).msg;
        let _169_m = _168___mcc_h2;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("ErrorState "), _169_m);
      }
    };
    Size() {
      let _this = this;
      return new BigNumber(((_this).dtor_stack).length);
    };
    PC() {
      let _this = this;
      return (_this).dtor_pc;
    };
    Skip(n) {
      let _this = this;
      let _170_dt__update__tmp_h0 = _this;
      let _171_dt__update_hpc_h0 = ((_this).dtor_pc).plus(n);
      return State.AState.create_EState(_171_dt__update_hpc_h0, (_170_dt__update__tmp_h0).dtor_stack);
    };
    Goto(tgt) {
      let _this = this;
      let _172_dt__update__tmp_h0 = _this;
      let _173_dt__update_hpc_h0 = tgt;
      return State.AState.create_EState(_173_dt__update_hpc_h0, (_172_dt__update__tmp_h0).dtor_stack);
    };
    Peek(k) {
      let _this = this;
      return ((_this).dtor_stack)[k];
    };
    Pop() {
      let _this = this;
      return (_this).PopN(_dafny.ONE);
    };
    PopN(n) {
      let _this = this;
      let _174_dt__update__tmp_h0 = _this;
      let _175_dt__update_hstack_h0 = ((_this).dtor_stack).slice(n);
      return State.AState.create_EState((_174_dt__update__tmp_h0).dtor_pc, _175_dt__update_hstack_h0);
    };
    Push(v) {
      let _this = this;
      let _176_dt__update__tmp_h0 = _this;
      let _177_dt__update_hstack_h0 = _dafny.Seq.Concat(_dafny.Seq.of(v), (_this).dtor_stack);
      return State.AState.create_EState((_176_dt__update__tmp_h0).dtor_pc, _177_dt__update_hstack_h0);
    };
    PushNRandom(n) {
      let _this = this;
      let _178_xr = _dafny.Seq.Create(n, function (_179___v0) {
        return StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString(""));
      });
      let _180_dt__update__tmp_h0 = _this;
      let _181_dt__update_hstack_h0 = _dafny.Seq.Concat(_178_xr, (_this).dtor_stack);
      return State.AState.create_EState((_180_dt__update__tmp_h0).dtor_pc, _181_dt__update_hstack_h0);
    };
    Dup(n) {
      let _this = this;
      let _182_nth = ((_this).dtor_stack)[(n).minus(_dafny.ONE)];
      let _183_dt__update__tmp_h0 = _this;
      let _184_dt__update_hstack_h0 = _dafny.Seq.Concat(_dafny.Seq.of(_182_nth), (_this).dtor_stack);
      return State.AState.create_EState((_183_dt__update__tmp_h0).dtor_pc, _184_dt__update_hstack_h0);
    };
    Swap(n) {
      let _this = this;
      let _185_nth = ((_this).dtor_stack)[n];
      let _186_top = ((_this).dtor_stack)[_dafny.ZERO];
      let _187_dt__update__tmp_h0 = _this;
      let _188_dt__update_hstack_h0 = _dafny.Seq.update(_dafny.Seq.update((_this).dtor_stack, _dafny.ZERO, _185_nth), n, _186_top);
      return State.AState.create_EState((_187_dt__update__tmp_h0).dtor_pc, _188_dt__update_hstack_h0);
    };
    Sat(c) {
      let _this = this;
      if (((c).Size()).isEqualTo(_dafny.ONE)) {
        return State.__default.checkPos(_this, ((c).dtor_trackedPos)[_dafny.ZERO], ((c).dtor_trackedVals)[_dafny.ZERO]);
      } else {
        return (State.__default.checkPos(_this, ((c).dtor_trackedPos)[_dafny.ZERO], ((c).dtor_trackedVals)[_dafny.ZERO])) && ((_this).Sat((c).Tail()));
      }
    };
  }
  return $module;
})(); // end of module State
let EVMToolTips = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "EVMToolTips._default";
    }
    _parentTraits() {
      return [];
    }
    static ToolTip(op) {
      if ((op) === (0)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Halts the machine without return output data"), new BigNumber(32));
      } else if ((op) === (1)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer addition modulo TWO_256"), new BigNumber(40));
      } else if ((op) === (2)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer multiplication modulo TWO_256"), new BigNumber(61));
      } else if ((op) === (3)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer subtraction modulo TWO_256"), new BigNumber(81));
      } else if ((op) === (4)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer division modulo TWO_256. Div by 0 yields 0"), new BigNumber(154));
      } else if ((op) === (5)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Signed integer division modulo TWO_256. Div by 0 yields 0"), new BigNumber(173));
      } else if ((op) === (6)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned modulo remainder"), new BigNumber(195));
      } else if ((op) === (7)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Signed modulo remainder"), new BigNumber(211));
      } else if ((op) === (8)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer addition modulo"), new BigNumber(230));
      } else if ((op) === (9)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned integer multiplication modulo"), new BigNumber(250));
      } else if ((op) === (10)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Exponential"), new BigNumber(272));
      } else if ((op) === (11)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Extend length of two's complement signed integer"), new BigNumber(291));
      } else if ((op) === (16)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned Less than"), new BigNumber(314));
      } else if ((op) === (17)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Unsigned Greater than"), new BigNumber(336));
      } else if ((op) === (18)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Signed less than"), new BigNumber(358));
      } else if ((op) === (19)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Signed greater than"), new BigNumber(380));
      } else if ((op) === (20)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("equal"), new BigNumber(402));
      } else if ((op) === (21)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Is equal to zero"), new BigNumber(424));
      } else if ((op) === (22)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Bitwise AND"), new BigNumber(445));
      } else if ((op) === (23)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Bitwise OR"), new BigNumber(464));
      } else if ((op) === (24)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Bitwise XOR"), new BigNumber(484));
      } else if ((op) === (25)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Bitwise NOT"), new BigNumber(504));
      } else if ((op) === (26)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Extract a byte from a word."), new BigNumber(522));
      } else if ((op) === (27)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Left shift"), new BigNumber(541));
      } else if ((op) === (28)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Right shift"), new BigNumber(560));
      } else if ((op) === (29)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Arithmetic (signed) right shift operation"), new BigNumber(579));
      } else if ((op) === (32)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Keccak 256 hash"), new BigNumber(598));
      } else if ((op) === (48)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Address of current executing account"), new BigNumber(640));
      } else if ((op) === (49)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Balance of a given account"), new BigNumber(655));
      } else if ((op) === (50)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Originator's address"), new BigNumber(676));
      } else if ((op) === (51)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Caller address"), new BigNumber(692));
      } else if ((op) === (52)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Value deposited by function call"), new BigNumber(707));
      } else if ((op) === (53)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Input data for this call"), new BigNumber(723));
      } else if ((op) === (54)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Size of the input data"), new BigNumber(742));
      } else if ((op) === (55)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Copy input data to memory"), new BigNumber(759));
      } else if ((op) === (56)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Size of the code of this contract"), new BigNumber(783));
      } else if ((op) === (57)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Copy the executing code to memory"), new BigNumber(799));
      } else if ((op) === (58)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Gas price in current block"), new BigNumber(824));
      } else if ((op) === (59)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Size of the calling account's code"), new BigNumber(839));
      } else if ((op) === (60)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Copy account's code to memory"), new BigNumber(866));
      } else if ((op) === (61)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Size of return data from previous call"), new BigNumber(920));
      } else if ((op) === (62)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Copy return data from previous call to memory"), new BigNumber(937));
      } else if ((op) === (63)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Hash of account's code"), new BigNumber(895));
      } else if ((op) === (64)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Hash of current block"), new BigNumber(626));
      } else if ((op) === (65)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Current block's beneficiay address"), new BigNumber(970));
      } else if ((op) === (66)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Current block's timestamp"), new BigNumber(985));
      } else if ((op) === (67)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Current block's number"), new BigNumber(1000));
      } else if ((op) === (68)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Current block's difficulty"), new BigNumber(1015));
      } else if ((op) === (69)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Current block's gas limit"), new BigNumber(1030));
      } else if ((op) === (70)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Chain ID"), new BigNumber(1045));
      } else if ((op) === (71)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Balance of currently executing account"), new BigNumber(1060));
      } else if ((op) === (72)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Base fee for the currently executing block"), new BigNumber(1080));
      } else if ((op) === (80)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Pop top of stack"), new BigNumber(1097));
      } else if ((op) === (81)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Read a word from memory"), new BigNumber(1133));
      } else if ((op) === (82)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Store a word to memory"), new BigNumber(1165));
      } else if ((op) === (83)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Store a byte to memory"), new BigNumber(1195));
      } else if ((op) === (84)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Read a word from storage"), new BigNumber(1214));
      } else if ((op) === (85)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Store a word to storage"), new BigNumber(1233));
      } else if ((op) === (86)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Uncoditional Jump"), new BigNumber(1255));
      } else if ((op) === (87)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Conditional Jump"), new BigNumber(1277));
      } else if ((op) === (92)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Static relative jump using a given offset"), new BigNumber(1343));
      } else if ((op) === (93)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Conditional Static relative jump using a given offset"), new BigNumber(1363));
      } else if ((op) === (94)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Relative jump via a jump table of one or more relative offsets"), new BigNumber(1392));
      } else if ((op) === (88)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Value of program counter"), new BigNumber(1302));
      } else if ((op) === (89)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Size of allocated memory"), new BigNumber(1113));
      } else if ((op) === (90)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Amount of available gas"), new BigNumber(1318));
      } else if ((op) === (91)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("A valid destination for a jump"), new BigNumber(1334));
      } else if ((op) === (95)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 0 on stack"), new BigNumber(1428));
      } else if ((op) === (96)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 1 byte"), new BigNumber(1479));
      } else if ((op) === (97)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 2 bytes"), new BigNumber(1486));
      } else if ((op) === (98)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 3 bytes"), new BigNumber(1493));
      } else if ((op) === (99)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 4 bytes"), new BigNumber(1500));
      } else if ((op) === (100)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 5 bytes"), new BigNumber(1507));
      } else if ((op) === (101)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 6 bytes"), new BigNumber(1514));
      } else if ((op) === (102)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 7 bytes"), new BigNumber(1521));
      } else if ((op) === (103)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 8 bytes"), new BigNumber(1528));
      } else if ((op) === (104)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 9 bytes"), new BigNumber(1535));
      } else if ((op) === (105)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 10 bytes"), new BigNumber(1535));
      } else if ((op) === (106)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 11 bytes"), new BigNumber(1535));
      } else if ((op) === (107)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 12 bytes"), new BigNumber(1535));
      } else if ((op) === (108)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 13 bytes"), new BigNumber(1535));
      } else if ((op) === (109)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 14 bytes"), new BigNumber(1535));
      } else if ((op) === (110)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 15 bytes"), new BigNumber(1535));
      } else if ((op) === (111)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 16 bytes"), new BigNumber(1535));
      } else if ((op) === (112)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 17 bytes"), new BigNumber(1535));
      } else if ((op) === (113)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 18 bytes"), new BigNumber(1535));
      } else if ((op) === (114)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 19 bytes"), new BigNumber(1535));
      } else if ((op) === (115)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 20 bytes"), new BigNumber(1535));
      } else if ((op) === (116)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 21 bytes"), new BigNumber(1535));
      } else if ((op) === (117)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 22 bytes"), new BigNumber(1535));
      } else if ((op) === (118)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 23 bytes"), new BigNumber(1535));
      } else if ((op) === (119)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 24 bytes"), new BigNumber(1535));
      } else if ((op) === (120)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 25 bytes"), new BigNumber(1535));
      } else if ((op) === (121)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 26 bytes"), new BigNumber(1535));
      } else if ((op) === (122)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 27 bytes"), new BigNumber(1535));
      } else if ((op) === (123)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 28 bytes"), new BigNumber(1535));
      } else if ((op) === (124)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 29 bytes"), new BigNumber(1535));
      } else if ((op) === (125)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 30 bytes"), new BigNumber(1535));
      } else if ((op) === (126)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 31 bytes"), new BigNumber(1535));
      } else if ((op) === (127)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Push 32 bytes"), new BigNumber(1535));
      } else if ((op) === (128)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 1st element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (129)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 2nd element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (130)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 3rd element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (131)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 4-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (132)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 5-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (133)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 6-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (134)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 7-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (135)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 8-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (136)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 9-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (137)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 10-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (138)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 11-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (139)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 12-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (140)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 13-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (141)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 14-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (142)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 15-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (143)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Duplicate 16-th element on top of the stack"), new BigNumber(1568));
      } else if ((op) === (144)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 2nd element of the stack"), new BigNumber(1577));
      } else if ((op) === (145)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 3rd element of the stack"), new BigNumber(1577));
      } else if ((op) === (146)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 4-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (147)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 5-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (148)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 6-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (149)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 7-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (150)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 8-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (151)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 9-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (152)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 10-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (153)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 11-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (154)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 12-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (155)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 13-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (156)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 14-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (157)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 15-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (158)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 16-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (159)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Swap top and 17-th element of the stack"), new BigNumber(1577));
      } else if ((op) === (160)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Append log with 0 topics"), new BigNumber(1600));
      } else if ((op) === (161)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Append log with 1 topics"), new BigNumber(1600));
      } else if ((op) === (162)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Append log with 2 topics"), new BigNumber(1600));
      } else if ((op) === (163)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Append log with 3 topics"), new BigNumber(1600));
      } else if ((op) === (164)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Append log with 4 topics"), new BigNumber(1600));
      } else if ((op) === (240)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Create a new account with associated code"), new BigNumber(1629));
      } else if ((op) === (241)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Message-call into an account"), new BigNumber(1674));
      } else if ((op) === (242)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Message-call into this account with another account's code"), new BigNumber(1711));
      } else if ((op) === (243)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Halt execution and return data"), new BigNumber(1742));
      } else if ((op) === (244)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Message-call into this account with an alternative account's code"), new BigNumber(1764));
      } else if ((op) === (245)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Create a new account with associated code"), new BigNumber(1799));
      } else if ((op) === (250)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Static Message-call into an account"), new BigNumber(1844));
      } else if ((op) === (253)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Revert execution and return data"), new BigNumber(1874));
      } else if ((op) === (255)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Delete this account"), new BigNumber(1896));
      } else if ((op) === (254)) {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("Equivalent to STOP"), new BigNumber(32));
      } else {
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("N/A"), _dafny.ZERO);
      }
    };
    static Gas(op) {
      if ((op) === (0)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__ZERO);
      } else if ((op) === (1)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (2)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (3)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (4)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (5)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (6)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (7)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (8)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__MID);
      } else if ((op) === (9)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__MID);
      } else if ((op) === (10)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (11)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (16)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (17)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (18)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (19)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (20)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (21)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (22)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (23)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (24)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (25)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (26)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (27)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (28)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (29)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (32)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (48)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (50)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (51)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (52)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (53)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (54)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (55)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (56)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (57)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (58)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (59)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (60)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (61)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (62)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (63)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (64)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BLOCKHASH);
      } else if ((op) === (65)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (66)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (67)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (68)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (69)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (70)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (71)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__LOW);
      } else if ((op) === (72)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (80)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (81)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (82)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (83)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (84)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (85)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (86)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__MID);
      } else if ((op) === (87)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__HIGH);
      } else if ((op) === (88)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (89)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (90)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__BASE);
      } else if ((op) === (91)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__JUMPDEST);
      } else if ((op) === (95)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (96)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (97)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (98)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (99)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (100)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (101)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (102)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (103)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (104)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (105)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (106)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (107)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (108)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (109)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (110)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (111)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (112)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (113)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (114)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (115)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (116)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (117)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (118)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (119)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (120)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (121)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (122)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (123)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (124)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (125)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (126)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (127)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (128)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (129)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (130)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (131)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (132)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (133)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (134)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (135)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (136)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (137)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (138)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (139)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (140)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (141)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (142)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (143)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (144)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (145)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (146)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (147)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (148)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (149)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (150)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (151)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (152)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (153)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (154)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (155)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (156)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (157)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (158)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (159)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else if ((op) === (160)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (161)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (162)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (163)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (164)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (240)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (241)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (242)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (243)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (244)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (245)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (250)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (253)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (255)) {
        return _dafny.Seq.UnicodeFromString("Depends on memory expansion");
      } else if ((op) === (254)) {
        return Int.__default.NatToString(EVMToolTips.__default.G__VERYLOW);
      } else {
        return _dafny.Seq.UnicodeFromString("Unknown opcode");
      }
    };
    static get G__ZERO() {
      return _dafny.ZERO;
    };
    static get G__VERYLOW() {
      return new BigNumber(3);
    };
    static get G__LOW() {
      return new BigNumber(5);
    };
    static get G__MID() {
      return new BigNumber(8);
    };
    static get G__BASE() {
      return new BigNumber(2);
    };
    static get G__BLOCKHASH() {
      return new BigNumber(20);
    };
    static get G__HIGH() {
      return new BigNumber(10);
    };
    static get G__JUMPDEST() {
      return _dafny.ONE;
    };
    static get bytecodeRefLine() {
      return _dafny.Seq.UnicodeFromString("https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/bytecode.dfy#L");
    };
    static get gasRefLine() {
      return _dafny.Seq.UnicodeFromString("https://github.com/Consensys/evm-dafny/blob/60bce44ee75978a4c97b9eab8e03424c9c233bbd/src/dafny/evm.dfy#L103");
    };
    static get G__WARMACCESS() {
      return new BigNumber(100);
    };
    static get G__COLDACCOUNTACCESS() {
      return new BigNumber(2600);
    };
    static get G__COLDSLOAD() {
      return new BigNumber(2100);
    };
    static get G__SSET() {
      return new BigNumber(20000);
    };
    static get G__SRESET() {
      return new BigNumber(2900);
    };
    static get R__SCLEAR() {
      return new BigNumber(15000);
    };
    static get R__SELFDESTRUCT() {
      return new BigNumber(24000);
    };
    static get G__SELFDESTRUCT() {
      return new BigNumber(5000);
    };
    static get G__CREATE() {
      return new BigNumber(32000);
    };
    static get G__CODEDEPOSIT() {
      return new BigNumber(200);
    };
    static get G__CALLVALUE() {
      return new BigNumber(9000);
    };
    static get G__CALLSTIPEND() {
      return new BigNumber(2300);
    };
    static get G__NEWACCOUNT() {
      return new BigNumber(25000);
    };
    static get G__EXP() {
      return new BigNumber(10);
    };
    static get G__EXPBYTE() {
      return new BigNumber(50);
    };
    static get G__MEMORY() {
      return new BigNumber(3);
    };
    static get G__TXCREATE() {
      return new BigNumber(32000);
    };
    static get G__TXDATAZERO() {
      return new BigNumber(4);
    };
    static get G__TXDATANONZERO() {
      return new BigNumber(16);
    };
    static get G__TRANSACTION() {
      return new BigNumber(21000);
    };
    static get G__LOG() {
      return new BigNumber(375);
    };
    static get G__LOGDATA() {
      return new BigNumber(8);
    };
    static get G__LOGTOPIC() {
      return new BigNumber(375);
    };
    static get G__KECCAK256() {
      return new BigNumber(30);
    };
    static get G__KECCAK256WORD() {
      return new BigNumber(6);
    };
    static get G__COPY() {
      return new BigNumber(3);
    };
  };
  return $module;
})(); // end of module EVMToolTips
let Instructions = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Instructions._default";
    }
    _parentTraits() {
      return [];
    }
    static GetArgValuePush(xc) {
      let _189_pad = _dafny.Seq.Create((new BigNumber(64)).minus(new BigNumber((xc).length)), function (_190___v149) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      });
      return (Hex.__default.HexToU256(_dafny.Seq.Concat(_189_pad, xc))).Extract();
    };
    static Colours(i) {
      let _source32 = (i).dtor_op;
      if (_source32.is_ArithOp) {
        let _191___mcc_h0 = (_source32).name;
        let _192___mcc_h1 = (_source32).opcode;
        let _193___mcc_h2 = (_source32).minCapacity;
        let _194___mcc_h3 = (_source32).minOperands;
        let _195___mcc_h4 = (_source32).pushes;
        let _196___mcc_h5 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("#316152"), _dafny.Seq.UnicodeFromString("#c6eb76"));
      } else if (_source32.is_CompOp) {
        let _197___mcc_h6 = (_source32).name;
        let _198___mcc_h7 = (_source32).opcode;
        let _199___mcc_h8 = (_source32).minCapacity;
        let _200___mcc_h9 = (_source32).minOperands;
        let _201___mcc_h10 = (_source32).pushes;
        let _202___mcc_h11 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("darkgoldenrod"), _dafny.Seq.UnicodeFromString("bisque"));
      } else if (_source32.is_BitwiseOp) {
        let _203___mcc_h12 = (_source32).name;
        let _204___mcc_h13 = (_source32).opcode;
        let _205___mcc_h14 = (_source32).minCapacity;
        let _206___mcc_h15 = (_source32).minOperands;
        let _207___mcc_h16 = (_source32).pushes;
        let _208___mcc_h17 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("orange"), _dafny.Seq.UnicodeFromString("#f3f383"));
      } else if (_source32.is_KeccakOp) {
        let _209___mcc_h18 = (_source32).name;
        let _210___mcc_h19 = (_source32).opcode;
        let _211___mcc_h20 = (_source32).minCapacity;
        let _212___mcc_h21 = (_source32).minOperands;
        let _213___mcc_h22 = (_source32).pushes;
        let _214___mcc_h23 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("grey"), _dafny.Seq.UnicodeFromString("linen"));
      } else if (_source32.is_EnvOp) {
        let _215___mcc_h24 = (_source32).name;
        let _216___mcc_h25 = (_source32).opcode;
        let _217___mcc_h26 = (_source32).minCapacity;
        let _218___mcc_h27 = (_source32).minOperands;
        let _219___mcc_h28 = (_source32).pushes;
        let _220___mcc_h29 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("darkslategrey"), _dafny.Seq.UnicodeFromString("lightgrey"));
      } else if (_source32.is_MemOp) {
        let _221___mcc_h30 = (_source32).name;
        let _222___mcc_h31 = (_source32).opcode;
        let _223___mcc_h32 = (_source32).minCapacity;
        let _224___mcc_h33 = (_source32).minOperands;
        let _225___mcc_h34 = (_source32).pushes;
        let _226___mcc_h35 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("sienna"), _dafny.Seq.UnicodeFromString("wheat"));
      } else if (_source32.is_StorageOp) {
        let _227___mcc_h36 = (_source32).name;
        let _228___mcc_h37 = (_source32).opcode;
        let _229___mcc_h38 = (_source32).minCapacity;
        let _230___mcc_h39 = (_source32).minOperands;
        let _231___mcc_h40 = (_source32).pushes;
        let _232___mcc_h41 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("fuchsia"), _dafny.Seq.UnicodeFromString("mistyrose"));
      } else if (_source32.is_JumpOp) {
        let _233___mcc_h42 = (_source32).name;
        let _234___mcc_h43 = (_source32).opcode;
        let _235___mcc_h44 = (_source32).minCapacity;
        let _236___mcc_h45 = (_source32).minOperands;
        let _237___mcc_h46 = (_source32).pushes;
        let _238___mcc_h47 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("purple"), _dafny.Seq.UnicodeFromString("thistle"));
      } else if (_source32.is_RunOp) {
        let _239___mcc_h48 = (_source32).name;
        let _240___mcc_h49 = (_source32).opcode;
        let _241___mcc_h50 = (_source32).minCapacity;
        let _242___mcc_h51 = (_source32).minOperands;
        let _243___mcc_h52 = (_source32).pushes;
        let _244___mcc_h53 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("sienna"), _dafny.Seq.UnicodeFromString("tan"));
      } else if (_source32.is_StackOp) {
        let _245___mcc_h54 = (_source32).name;
        let _246___mcc_h55 = (_source32).opcode;
        let _247___mcc_h56 = (_source32).minCapacity;
        let _248___mcc_h57 = (_source32).minOperands;
        let _249___mcc_h58 = (_source32).pushes;
        let _250___mcc_h59 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("royalblue"), _dafny.Seq.UnicodeFromString("powderblue"));
      } else if (_source32.is_LogOp) {
        let _251___mcc_h60 = (_source32).name;
        let _252___mcc_h61 = (_source32).opcode;
        let _253___mcc_h62 = (_source32).minCapacity;
        let _254___mcc_h63 = (_source32).minOperands;
        let _255___mcc_h64 = (_source32).pushes;
        let _256___mcc_h65 = (_source32).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("cornflowerblue"), _dafny.Seq.UnicodeFromString("lavender"));
      } else {
        let _257___mcc_h66 = (_source32).name;
        let _258___mcc_h67 = (_source32).opcode;
        let _259___mcc_h68 = (_source32).minCapacity;
        let _260___mcc_h69 = (_source32).minOperands;
        let _261___mcc_h70 = (_source32).pushes;
        let _262___mcc_h71 = (_source32).pops;
        let _263_opcode = _258___mcc_h67;
        if (((_263_opcode) === (EVMConstants.__default.STOP)) || ((_263_opcode) === (EVMConstants.__default.REVERT))) {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("brown"), _dafny.Seq.UnicodeFromString("lightsalmon"));
        } else if ((_263_opcode) === (EVMConstants.__default.RETURN)) {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("teal"), _dafny.Seq.UnicodeFromString("greenyellow"));
        } else if (((((_263_opcode) === (EVMConstants.__default.CALL)) || ((_263_opcode) === (EVMConstants.__default.CALLCODE))) || ((_263_opcode) === (EVMConstants.__default.DELEGATECALL))) || ((_263_opcode) === (EVMConstants.__default.STATICCALL))) {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("sienna"), _dafny.Seq.UnicodeFromString("tan"));
        } else {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("brown"), _dafny.Seq.UnicodeFromString("salmon"));
        }
      }
    };
  };

  $module.ValidInstruction = class ValidInstruction {
    constructor () {
    }
    static get Witness() {
      return Instructions.Instruction.create_Instruction(EVMOpcodes.Opcode.create_SysOp(_dafny.Seq.UnicodeFromString("STOP"), EVMConstants.__default.STOP, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO), _dafny.Seq.of(), _dafny.ZERO);
    }
    static get Default() {
      return Instructions.ValidInstruction.Witness;
    }
  };

  $module.Instruction = class Instruction {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Instruction(op, arg, address) {
      let $dt = new Instruction(0);
      $dt.op = op;
      $dt.arg = arg;
      $dt.address = address;
      return $dt;
    }
    get is_Instruction() { return this.$tag === 0; }
    get dtor_op() { return this.op; }
    get dtor_arg() { return this.arg; }
    get dtor_address() { return this.address; }
    toString() {
      if (this.$tag === 0) {
        return "Instructions.Instruction.Instruction" + "(" + _dafny.toString(this.op) + ", " + this.arg.toVerbatimString(true) + ", " + _dafny.toString(this.address) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.op, other.op) && _dafny.areEqual(this.arg, other.arg) && _dafny.areEqual(this.address, other.address);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Instructions.Instruction.create_Instruction(EVMOpcodes.ValidOpcode.Default, '', _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Instruction.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      return ((((_this).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID)) || ((!(((EVMConstants.__default.PUSH0) <= (((_this).dtor_op).dtor_opcode)) && ((((_this).dtor_op).dtor_opcode) <= (EVMConstants.__default.PUSH32))) || (((new BigNumber(((_this).dtor_arg).length)).isEqualTo((new BigNumber(2)).multipliedBy(new BigNumber((((_this).dtor_op).dtor_opcode) - (EVMConstants.__default.PUSH0))))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((_this).dtor_arg).length)), true, function (_forall_var_2) {
        let _264_k = _forall_var_2;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_264_k)) && ((_264_k).isLessThan(new BigNumber(((_this).dtor_arg).length)))) || (Hex.__default.IsHex(((_this).dtor_arg)[_264_k]));
      })))) && (!(!(((EVMConstants.__default.PUSH0) <= (((_this).dtor_op).dtor_opcode)) && ((((_this).dtor_op).dtor_opcode) <= (EVMConstants.__default.PUSH32)))) || ((new BigNumber(((_this).dtor_arg).length)).isEqualTo(_dafny.ZERO))));
    };
    ToString() {
      let _this = this;
      let _265_x = (_this).dtor_arg;
      if ((((_this).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(((_this).dtor_op).Name(), _dafny.Seq.UnicodeFromString(" ")), _265_x);
      } else {
        return _dafny.Seq.Concat(((_this).dtor_op).Name(), (((_dafny.ZERO).isLessThan(new BigNumber((_265_x).length))) ? (_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" 0x"), _265_x)) : (_dafny.Seq.UnicodeFromString(""))));
      }
    };
    ToHTML() {
      let _this = this;
      let _266_x = (_this).dtor_arg;
      let _267_cols = Instructions.__default.Colours(_this);
      let _268_formattedAddress = _dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber((Hex.__default.NatToHex((_this).dtor_address)).length)).mod(new BigNumber(2)), function (_269___v0) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      }), Hex.__default.NatToHex((_this).dtor_address));
      let _270_insText = (((((_this).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), (_267_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), _dafny.Seq.UnicodeFromString(" ")), _266_x)) : (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), (_267_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), (((_dafny.ZERO).isLessThan(new BigNumber((_266_x).length))) ? (_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" 0x"), _266_x)) : (_dafny.Seq.UnicodeFromString(""))))));
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("0x"), _268_formattedAddress), _dafny.Seq.UnicodeFromString(":")), _270_insText), _dafny.Seq.UnicodeFromString(" <BR ALIGN=\"LEFT\"/>\n"));
    };
    ToHTMLTable(entryPortTag, exitPortTag) {
      let _this = this;
      let _271_cols = Instructions.__default.Colours(_this);
      let _272_formattedAddress = _dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber((Hex.__default.NatToHex((_this).dtor_address)).length)).mod(new BigNumber(2)), function (_273___v1) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      }), Hex.__default.NatToHex((_this).dtor_address));
      let _274_gasLine = _dafny.Seq.UnicodeFromString("&#9981;");
      let _275_oplineTD = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "), entryPortTag), _dafny.Seq.UnicodeFromString(">")), _dafny.Seq.UnicodeFromString("0x")), _272_formattedAddress), _dafny.Seq.UnicodeFromString(" </TD>\n")), _dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")), EVMToolTips.__default.Gas(((_this).dtor_op).dtor_opcode)), _dafny.Seq.UnicodeFromString(" \" ")), _dafny.Seq.UnicodeFromString("target=\"_blank\" href=\"")), EVMToolTips.__default.gasRefLine), _dafny.Seq.UnicodeFromString("\"")), _dafny.Seq.UnicodeFromString(">")), _274_gasLine), _dafny.Seq.UnicodeFromString("</TD>")), _dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")), (_271_cols)[1]), _dafny.Seq.UnicodeFromString("\" align=\"left\" cellpadding=\"3\" ")), exitPortTag), _dafny.Seq.UnicodeFromString(" href=\"")), EVMToolTips.__default.bytecodeRefLine), Int.__default.NatToString((EVMToolTips.__default.ToolTip(((_this).dtor_op).dtor_opcode))[1])), _dafny.Seq.UnicodeFromString("\" target=\"_blank\" ")), _dafny.Seq.UnicodeFromString(" tooltip=\"")), (EVMToolTips.__default.ToolTip(((_this).dtor_op).dtor_opcode))[0]), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString(">")), _dafny.Seq.UnicodeFromString("<FONT color=\"")), (_271_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), _dafny.Seq.UnicodeFromString("</TD>"));
      let _276_arglineTD = (((_dafny.ZERO).isLessThan(new BigNumber(((_this).dtor_arg).length))) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"true\" align=\"left\">"), _dafny.Seq.UnicodeFromString("  0x")), (_this).dtor_arg), _dafny.Seq.UnicodeFromString("</TD>"))) : (_dafny.Seq.UnicodeFromString("")));
      let _277_lineTR = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TR>"), _275_oplineTD), _276_arglineTD), _dafny.Seq.UnicodeFromString("</TR>"));
      let _278_itemTable = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TABLE  border=\"0\" cellpadding=\"0\" cellsborder=\"0\" CELLSPACING=\"1\">"), _277_lineTR), _dafny.Seq.UnicodeFromString("</TABLE>"));
      return _278_itemTable;
    };
    IsTerminal() {
      let _this = this;
      return ((_this).dtor_op).IsTerminal();
    };
    IsJumpDest() {
      let _this = this;
      return ((_this).dtor_op).IsJumpDest();
    };
    IsJump() {
      let _this = this;
      return ((_this).dtor_op).IsJump();
    };
    StackEffect() {
      let _this = this;
      return ((_this).dtor_op).StackEffect();
    };
    WeakestPreOperands(post) {
      let _this = this;
      return ((_this).dtor_op).WeakestPreOperands(post);
    };
    WeakestPreCapacity(post) {
      let _this = this;
      return ((_this).dtor_op).WeakestPreCapacity(post);
    };
    StackPosBackWardTracker(pos_k) {
      let _this = this;
      let _source33 = (_this).dtor_op;
      if (_source33.is_ArithOp) {
        let _279___mcc_h0 = (_source33).name;
        let _280___mcc_h1 = (_source33).opcode;
        let _281___mcc_h2 = (_source33).minCapacity;
        let _282___mcc_h3 = (_source33).minOperands;
        let _283___mcc_h4 = (_source33).pushes;
        let _284___mcc_h5 = (_source33).pops;
        let _285_pops = _284___mcc_h5;
        let _286_pushes = _283___mcc_h4;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Arithmetic operator with target 0")));
        }
      } else if (_source33.is_CompOp) {
        let _287___mcc_h6 = (_source33).name;
        let _288___mcc_h7 = (_source33).opcode;
        let _289___mcc_h8 = (_source33).minCapacity;
        let _290___mcc_h9 = (_source33).minOperands;
        let _291___mcc_h10 = (_source33).pushes;
        let _292___mcc_h11 = (_source33).pops;
        let _293_pops = _292___mcc_h11;
        let _294_pushes = _291___mcc_h10;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right(((pos_k).plus(_293_pops)).minus(_294_pushes));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Comparison operator with target 0")));
        }
      } else if (_source33.is_BitwiseOp) {
        let _295___mcc_h12 = (_source33).name;
        let _296___mcc_h13 = (_source33).opcode;
        let _297___mcc_h14 = (_source33).minCapacity;
        let _298___mcc_h15 = (_source33).minOperands;
        let _299___mcc_h16 = (_source33).pushes;
        let _300___mcc_h17 = (_source33).pops;
        let _301_pops = _300___mcc_h17;
        let _302_pushes = _299___mcc_h16;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right(((pos_k).plus(_301_pops)).minus(_302_pushes));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Bitwise operator with target 0")));
        }
      } else if (_source33.is_KeccakOp) {
        let _303___mcc_h18 = (_source33).name;
        let _304___mcc_h19 = (_source33).opcode;
        let _305___mcc_h20 = (_source33).minCapacity;
        let _306___mcc_h21 = (_source33).minOperands;
        let _307___mcc_h22 = (_source33).pushes;
        let _308___mcc_h23 = (_source33).pops;
        let _309_pops = _308___mcc_h23;
        let _310_pushes = _307___mcc_h22;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Keccak operator with target 0")));
        }
      } else if (_source33.is_EnvOp) {
        let _311___mcc_h24 = (_source33).name;
        let _312___mcc_h25 = (_source33).opcode;
        let _313___mcc_h26 = (_source33).minCapacity;
        let _314___mcc_h27 = (_source33).minOperands;
        let _315___mcc_h28 = (_source33).pushes;
        let _316___mcc_h29 = (_source33).pops;
        let _317_pops = _316___mcc_h29;
        let _318_pushes = _315___mcc_h28;
        if (((_318_pushes).isEqualTo(_dafny.ONE)) && ((_317_pops).isEqualTo(_dafny.ZERO))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Env operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
          }
        } else if (((_318_pushes).isEqualTo(_dafny.ONE)) && ((_317_pops).isEqualTo(_dafny.ONE))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Env operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        } else {
          return MiscTypes.Either.create_Right(((pos_k).plus(_317_pops)).minus(_318_pushes));
        }
      } else if (_source33.is_MemOp) {
        let _319___mcc_h30 = (_source33).name;
        let _320___mcc_h31 = (_source33).opcode;
        let _321___mcc_h32 = (_source33).minCapacity;
        let _322___mcc_h33 = (_source33).minOperands;
        let _323___mcc_h34 = (_source33).pushes;
        let _324___mcc_h35 = (_source33).pops;
        let _325_pops = _324___mcc_h35;
        let _326_pushes = _323___mcc_h34;
        if ((_326_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(2)));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Mem operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        }
      } else if (_source33.is_StorageOp) {
        let _327___mcc_h36 = (_source33).name;
        let _328___mcc_h37 = (_source33).opcode;
        let _329___mcc_h38 = (_source33).minCapacity;
        let _330___mcc_h39 = (_source33).minOperands;
        let _331___mcc_h40 = (_source33).pushes;
        let _332___mcc_h41 = (_source33).pops;
        let _333_pops = _332___mcc_h41;
        let _334_pushes = _331___mcc_h40;
        if ((_334_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(2)));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Storage operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        }
      } else if (_source33.is_JumpOp) {
        let _335___mcc_h42 = (_source33).name;
        let _336___mcc_h43 = (_source33).opcode;
        let _337___mcc_h44 = (_source33).minCapacity;
        let _338___mcc_h45 = (_source33).minOperands;
        let _339___mcc_h46 = (_source33).pushes;
        let _340___mcc_h47 = (_source33).pops;
        let _341_opcode = _336___mcc_h43;
        if ((_341_opcode) === (EVMConstants.__default.JUMPDEST)) {
          return MiscTypes.Either.create_Right(pos_k);
        } else if (((EVMConstants.__default.JUMP) <= (_341_opcode)) && ((_341_opcode) <= (EVMConstants.__default.JUMPI))) {
          let _342_k = ((_341_opcode) - (EVMConstants.__default.JUMP)) + (1);
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(_342_k)));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("Not implemented")));
        }
      } else if (_source33.is_RunOp) {
        let _343___mcc_h48 = (_source33).name;
        let _344___mcc_h49 = (_source33).opcode;
        let _345___mcc_h50 = (_source33).minCapacity;
        let _346___mcc_h51 = (_source33).minOperands;
        let _347___mcc_h52 = (_source33).pushes;
        let _348___mcc_h53 = (_source33).pops;
        let _349_pops = _348___mcc_h53;
        let _350_pushes = _347___mcc_h52;
        if ((pos_k).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Run operator with target 0")));
        } else {
          return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
        }
      } else if (_source33.is_StackOp) {
        let _351___mcc_h54 = (_source33).name;
        let _352___mcc_h55 = (_source33).opcode;
        let _353___mcc_h56 = (_source33).minCapacity;
        let _354___mcc_h57 = (_source33).minOperands;
        let _355___mcc_h58 = (_source33).pushes;
        let _356___mcc_h59 = (_source33).pops;
        let _357_opcode = _352___mcc_h55;
        if (((EVMConstants.__default.PUSH0) <= (_357_opcode)) && ((_357_opcode) <= (EVMConstants.__default.PUSH32))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Value(Instructions.__default.GetArgValuePush((_this).dtor_arg)));
          } else {
            return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
          }
        } else if (((EVMConstants.__default.DUP1) <= (_357_opcode)) && ((_357_opcode) <= (EVMConstants.__default.DUP16))) {
          return MiscTypes.Either.create_Right((((pos_k).isEqualTo(_dafny.ZERO)) ? (new BigNumber((_357_opcode) - (EVMConstants.__default.DUP1))) : ((pos_k).minus(_dafny.ONE))));
        } else if (((EVMConstants.__default.SWAP1) <= (_357_opcode)) && ((_357_opcode) <= (EVMConstants.__default.SWAP16))) {
          let _358_k = (new BigNumber((_357_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE);
          return MiscTypes.Either.create_Right((((pos_k).isEqualTo(_dafny.ZERO)) ? (_358_k) : ((((pos_k).isEqualTo(_358_k)) ? (_dafny.ZERO) : (pos_k)))));
        } else {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        }
      } else if (_source33.is_LogOp) {
        let _359___mcc_h60 = (_source33).name;
        let _360___mcc_h61 = (_source33).opcode;
        let _361___mcc_h62 = (_source33).minCapacity;
        let _362___mcc_h63 = (_source33).minOperands;
        let _363___mcc_h64 = (_source33).pushes;
        let _364___mcc_h65 = (_source33).pops;
        let _365_pops = _364___mcc_h65;
        let _366_pushes = _363___mcc_h64;
        return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(2)));
      } else {
        let _367___mcc_h66 = (_source33).name;
        let _368___mcc_h67 = (_source33).opcode;
        let _369___mcc_h68 = (_source33).minCapacity;
        let _370___mcc_h69 = (_source33).minOperands;
        let _371___mcc_h70 = (_source33).pushes;
        let _372___mcc_h71 = (_source33).pops;
        let _373_pops = _372___mcc_h71;
        let _374_pushes = _371___mcc_h70;
        if ((_374_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_373_pops));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Sys operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right((pos_k).plus(_373_pops));
          }
        }
      }
    };
    NextState(s, cond) {
      let _this = this;
      let _source34 = (_this).dtor_op;
      if (_source34.is_ArithOp) {
        let _375___mcc_h0 = (_source34).name;
        let _376___mcc_h1 = (_source34).opcode;
        let _377___mcc_h2 = (_source34).minCapacity;
        let _378___mcc_h3 = (_source34).minOperands;
        let _379___mcc_h4 = (_source34).pushes;
        let _380___mcc_h5 = (_source34).pops;
        let _381_pops = _380___mcc_h5;
        let _382_pushes = _379___mcc_h4;
        if (((_381_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_381_pops)).PushNRandom(_382_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source34.is_CompOp) {
        let _383___mcc_h6 = (_source34).name;
        let _384___mcc_h7 = (_source34).opcode;
        let _385___mcc_h8 = (_source34).minCapacity;
        let _386___mcc_h9 = (_source34).minOperands;
        let _387___mcc_h10 = (_source34).pushes;
        let _388___mcc_h11 = (_source34).pops;
        let _389_pops = _388___mcc_h11;
        let _390_pushes = _387___mcc_h10;
        if (((_389_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_389_pops)).PushNRandom(_390_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source34.is_BitwiseOp) {
        let _391___mcc_h12 = (_source34).name;
        let _392___mcc_h13 = (_source34).opcode;
        let _393___mcc_h14 = (_source34).minCapacity;
        let _394___mcc_h15 = (_source34).minOperands;
        let _395___mcc_h16 = (_source34).pushes;
        let _396___mcc_h17 = (_source34).pops;
        let _397_pops = _396___mcc_h17;
        let _398_pushes = _395___mcc_h16;
        if (((_397_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_397_pops)).PushNRandom(_398_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source34.is_KeccakOp) {
        let _399___mcc_h18 = (_source34).name;
        let _400___mcc_h19 = (_source34).opcode;
        let _401___mcc_h20 = (_source34).minCapacity;
        let _402___mcc_h21 = (_source34).minOperands;
        let _403___mcc_h22 = (_source34).pushes;
        let _404___mcc_h23 = (_source34).pops;
        let _405_pops = _404___mcc_h23;
        let _406_pushes = _403___mcc_h22;
        if (((new BigNumber(2)).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(new BigNumber(2))).Push(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("")))).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source34.is_EnvOp) {
        let _407___mcc_h24 = (_source34).name;
        let _408___mcc_h25 = (_source34).opcode;
        let _409___mcc_h26 = (_source34).minCapacity;
        let _410___mcc_h27 = (_source34).minOperands;
        let _411___mcc_h28 = (_source34).pushes;
        let _412___mcc_h29 = (_source34).pops;
        let _413_pops = _412___mcc_h29;
        let _414_pushes = _411___mcc_h28;
        if (((_413_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_413_pops)).PushNRandom(_414_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("EnvOp error"));
        }
      } else if (_source34.is_MemOp) {
        let _415___mcc_h30 = (_source34).name;
        let _416___mcc_h31 = (_source34).opcode;
        let _417___mcc_h32 = (_source34).minCapacity;
        let _418___mcc_h33 = (_source34).minOperands;
        let _419___mcc_h34 = (_source34).pushes;
        let _420___mcc_h35 = (_source34).pops;
        let _421_pops = _420___mcc_h35;
        let _422_pushes = _419___mcc_h34;
        if (((_421_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_421_pops)).PushNRandom(_422_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("MemOp error"));
        }
      } else if (_source34.is_StorageOp) {
        let _423___mcc_h36 = (_source34).name;
        let _424___mcc_h37 = (_source34).opcode;
        let _425___mcc_h38 = (_source34).minCapacity;
        let _426___mcc_h39 = (_source34).minOperands;
        let _427___mcc_h40 = (_source34).pushes;
        let _428___mcc_h41 = (_source34).pops;
        let _429_pops = _428___mcc_h41;
        let _430_pushes = _427___mcc_h40;
        if (((_429_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_429_pops)).PushNRandom(_430_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Storage Op error"));
        }
      } else if (_source34.is_JumpOp) {
        let _431___mcc_h42 = (_source34).name;
        let _432___mcc_h43 = (_source34).opcode;
        let _433___mcc_h44 = (_source34).minCapacity;
        let _434___mcc_h45 = (_source34).minOperands;
        let _435___mcc_h46 = (_source34).pushes;
        let _436___mcc_h47 = (_source34).pops;
        let _437_pops = _436___mcc_h47;
        let _438_pushes = _435___mcc_h46;
        let _439_opcode = _432___mcc_h43;
        if ((_439_opcode) === (EVMConstants.__default.JUMPDEST)) {
          if (!(cond)) {
            return (s).Skip(_dafny.ONE);
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Cannot execute JUMPDEST/exit true"));
          }
        } else if ((_439_opcode) === (EVMConstants.__default.JUMP)) {
          if (((_dafny.ONE).isLessThanOrEqualTo((s).Size())) && (cond)) {
            let _source35 = (s).Peek(_dafny.ZERO);
            if (_source35.is_Value) {
              let _440___mcc_h72 = (_source35).v;
              let _441_v = _440___mcc_h72;
              return ((s).Pop()).Goto(_441_v);
            } else {
              let _442___mcc_h73 = (_source35).s;
              return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Jump to Random() error"));
            }
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Cannot execute JUMP/exit false or stack underflow"));
          }
        } else if ((_439_opcode) === (EVMConstants.__default.JUMPI)) {
          if ((new BigNumber(2)).isLessThanOrEqualTo((s).Size())) {
            let _source36 = (s).Peek(_dafny.ZERO);
            if (_source36.is_Value) {
              let _443___mcc_h74 = (_source36).v;
              let _444_v = _443___mcc_h74;
              if (cond) {
                return ((s).PopN(new BigNumber(2))).Goto(_444_v);
              } else {
                return ((s).PopN(new BigNumber(2))).Skip(_dafny.ONE);
              }
            } else {
              let _445___mcc_h75 = (_source36).s;
              return State.AState.create_Error(_dafny.Seq.UnicodeFromString("JumpI to Random() error"));
            }
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Cannot execute JUMPI/strack underflow"));
          }
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("RJUMPs not implemented"));
        }
      } else if (_source34.is_RunOp) {
        let _446___mcc_h48 = (_source34).name;
        let _447___mcc_h49 = (_source34).opcode;
        let _448___mcc_h50 = (_source34).minCapacity;
        let _449___mcc_h51 = (_source34).minOperands;
        let _450___mcc_h52 = (_source34).pushes;
        let _451___mcc_h53 = (_source34).pops;
        let _452_pops = _451___mcc_h53;
        let _453_pushes = _450___mcc_h52;
        if (!(cond)) {
          return ((s).Push(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("")))).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("RunOp error"));
        }
      } else if (_source34.is_StackOp) {
        let _454___mcc_h54 = (_source34).name;
        let _455___mcc_h55 = (_source34).opcode;
        let _456___mcc_h56 = (_source34).minCapacity;
        let _457___mcc_h57 = (_source34).minOperands;
        let _458___mcc_h58 = (_source34).pushes;
        let _459___mcc_h59 = (_source34).pops;
        let _460_pops = _459___mcc_h59;
        let _461_pushes = _458___mcc_h58;
        let _462_opcode = _455___mcc_h55;
        if ((((_462_opcode) === (EVMConstants.__default.POP)) && ((_dafny.ONE).isLessThanOrEqualTo((s).Size()))) && (!(cond))) {
          return ((s).Pop()).Skip(_dafny.ONE);
        } else if ((((EVMConstants.__default.PUSH0) <= (_462_opcode)) && ((_462_opcode) <= (EVMConstants.__default.PUSH32))) && (!(cond))) {
          return ((s).Push(StackElement.StackElem.create_Value(Instructions.__default.GetArgValuePush((_this).dtor_arg)))).Skip((_dafny.ONE).plus(new BigNumber((_462_opcode) - (EVMConstants.__default.PUSH0))));
        } else if (((((EVMConstants.__default.DUP1) <= (_462_opcode)) && ((_462_opcode) <= (EVMConstants.__default.DUP16))) && (((new BigNumber((_462_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE)).isLessThanOrEqualTo((s).Size()))) && (!(cond))) {
          return ((s).Dup((new BigNumber((_462_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE))).Skip(_dafny.ONE);
        } else if (((((EVMConstants.__default.SWAP1) <= (_462_opcode)) && ((_462_opcode) <= (EVMConstants.__default.SWAP16))) && (((new BigNumber((_462_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE)).isLessThan((s).Size()))) && (!(cond))) {
          return ((s).Swap((new BigNumber((_462_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE))).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack Op error"));
        }
      } else if (_source34.is_LogOp) {
        let _463___mcc_h60 = (_source34).name;
        let _464___mcc_h61 = (_source34).opcode;
        let _465___mcc_h62 = (_source34).minCapacity;
        let _466___mcc_h63 = (_source34).minOperands;
        let _467___mcc_h64 = (_source34).pushes;
        let _468___mcc_h65 = (_source34).pops;
        let _469_pops = _468___mcc_h65;
        let _470_pushes = _467___mcc_h64;
        if (((_469_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return ((s).PopN(_469_pops)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("LogOp error"));
        }
      } else {
        let _471___mcc_h66 = (_source34).name;
        let _472___mcc_h67 = (_source34).opcode;
        let _473___mcc_h68 = (_source34).minCapacity;
        let _474___mcc_h69 = (_source34).minOperands;
        let _475___mcc_h70 = (_source34).pushes;
        let _476___mcc_h71 = (_source34).pops;
        let _477_pops = _476___mcc_h71;
        let _478_pushes = _475___mcc_h70;
        let _479_op = _472___mcc_h67;
        if (((((_479_op) === (EVMConstants.__default.INVALID)) || ((_479_op) === (EVMConstants.__default.STOP))) || ((_479_op) === (EVMConstants.__default.RETURN))) || ((_479_op) === (EVMConstants.__default.REVERT))) {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("SysOp error"));
        } else if (((_477_pops).isLessThanOrEqualTo((s).Size())) && (!(cond))) {
          return (((s).PopN(_477_pops)).PushNRandom(_478_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("SysOp error"));
        }
      }
    };
    WPre(c) {
      let _this = this;
      let _source37 = (_this).dtor_op;
      if (_source37.is_ArithOp) {
        let _480___mcc_h0 = (_source37).name;
        let _481___mcc_h1 = (_source37).opcode;
        let _482___mcc_h2 = (_source37).minCapacity;
        let _483___mcc_h3 = (_source37).minOperands;
        let _484___mcc_h4 = (_source37).pushes;
        let _485___mcc_h5 = (_source37).pops;
        let _486_pops = _485___mcc_h5;
        let _487_pushes = _484___mcc_h4;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _488_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_489_pos) {
            return (_489_pos).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_488_shiftByOne, (c).TrackedVals());
        }
      } else if (_source37.is_CompOp) {
        let _490___mcc_h6 = (_source37).name;
        let _491___mcc_h7 = (_source37).opcode;
        let _492___mcc_h8 = (_source37).minCapacity;
        let _493___mcc_h9 = (_source37).minOperands;
        let _494___mcc_h10 = (_source37).pushes;
        let _495___mcc_h11 = (_source37).pops;
        let _496_pops = _495___mcc_h11;
        let _497_pushes = _494___mcc_h10;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _498_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_499_pops, _500_pushes) => function (_501_pos) {
            return ((_501_pos).plus(_499_pops)).minus(_500_pushes);
          })(_496_pops, _497_pushes));
          return WeakPre.Cond.create_StCond(_498_shiftBy, (c).TrackedVals());
        }
      } else if (_source37.is_BitwiseOp) {
        let _502___mcc_h12 = (_source37).name;
        let _503___mcc_h13 = (_source37).opcode;
        let _504___mcc_h14 = (_source37).minCapacity;
        let _505___mcc_h15 = (_source37).minOperands;
        let _506___mcc_h16 = (_source37).pushes;
        let _507___mcc_h17 = (_source37).pops;
        let _508_pops = _507___mcc_h17;
        let _509_pushes = _506___mcc_h16;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _510_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_511_pops, _512_pushes) => function (_513_pos) {
            return ((_513_pos).plus(_511_pops)).minus(_512_pushes);
          })(_508_pops, _509_pushes));
          return WeakPre.Cond.create_StCond(_510_shiftBy, (c).TrackedVals());
        }
      } else if (_source37.is_KeccakOp) {
        let _514___mcc_h18 = (_source37).name;
        let _515___mcc_h19 = (_source37).opcode;
        let _516___mcc_h20 = (_source37).minCapacity;
        let _517___mcc_h21 = (_source37).minOperands;
        let _518___mcc_h22 = (_source37).pushes;
        let _519___mcc_h23 = (_source37).pops;
        let _520_pops = _519___mcc_h23;
        let _521_pushes = _518___mcc_h22;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _522_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_523_pos) {
            return (_523_pos).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_522_shiftByOne, (c).TrackedVals());
        }
      } else if (_source37.is_EnvOp) {
        let _524___mcc_h24 = (_source37).name;
        let _525___mcc_h25 = (_source37).opcode;
        let _526___mcc_h26 = (_source37).minCapacity;
        let _527___mcc_h27 = (_source37).minOperands;
        let _528___mcc_h28 = (_source37).pushes;
        let _529___mcc_h29 = (_source37).pops;
        let _530_pops = _529___mcc_h29;
        let _531_pushes = _528___mcc_h28;
        if (((_531_pushes).isEqualTo(_dafny.ONE)) && ((_530_pops).isEqualTo(_dafny.ZERO))) {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            let _532_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_533_pos) {
              return (_533_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_532_shiftByOne, (c).TrackedVals());
          }
        } else if (((_531_pushes).isEqualTo(_dafny.ONE)) && ((_530_pops).isEqualTo(_dafny.ONE))) {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        } else {
          let _534_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_535_pops, _536_pushes) => function (_537_pos) {
            return ((_537_pos).plus(_535_pops)).minus(_536_pushes);
          })(_530_pops, _531_pushes));
          return WeakPre.Cond.create_StCond(_534_shiftBy, (c).TrackedVals());
        }
      } else if (_source37.is_MemOp) {
        let _538___mcc_h30 = (_source37).name;
        let _539___mcc_h31 = (_source37).opcode;
        let _540___mcc_h32 = (_source37).minCapacity;
        let _541___mcc_h33 = (_source37).minOperands;
        let _542___mcc_h34 = (_source37).pushes;
        let _543___mcc_h35 = (_source37).pops;
        let _544_pops = _543___mcc_h35;
        let _545_pushes = _542___mcc_h34;
        if ((_545_pushes).isEqualTo(_dafny.ZERO)) {
          let _546_shiftByTwo = MiscTypes.__default.Map((c).TrackedPos(), function (_547_pos) {
            return (_547_pos).plus(new BigNumber(2));
          });
          return WeakPre.Cond.create_StCond(_546_shiftByTwo, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        }
      } else if (_source37.is_StorageOp) {
        let _548___mcc_h36 = (_source37).name;
        let _549___mcc_h37 = (_source37).opcode;
        let _550___mcc_h38 = (_source37).minCapacity;
        let _551___mcc_h39 = (_source37).minOperands;
        let _552___mcc_h40 = (_source37).pushes;
        let _553___mcc_h41 = (_source37).pops;
        let _554_pops = _553___mcc_h41;
        let _555_pushes = _552___mcc_h40;
        if ((_555_pushes).isEqualTo(_dafny.ZERO)) {
          let _556_shiftByTwo = MiscTypes.__default.Map((c).TrackedPos(), function (_557_pos) {
            return (_557_pos).plus(new BigNumber(2));
          });
          return WeakPre.Cond.create_StCond(_556_shiftByTwo, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        }
      } else if (_source37.is_JumpOp) {
        let _558___mcc_h42 = (_source37).name;
        let _559___mcc_h43 = (_source37).opcode;
        let _560___mcc_h44 = (_source37).minCapacity;
        let _561___mcc_h45 = (_source37).minOperands;
        let _562___mcc_h46 = (_source37).pushes;
        let _563___mcc_h47 = (_source37).pops;
        let _564_opcode = _559___mcc_h43;
        if ((_564_opcode) === (EVMConstants.__default.JUMPDEST)) {
          return c;
        } else if (((EVMConstants.__default.JUMP) <= (_564_opcode)) && ((_564_opcode) <= (EVMConstants.__default.JUMPI))) {
          let _565_k = ((_564_opcode) - (EVMConstants.__default.JUMP)) + (1);
          let _566_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_567_k) => function (_568_pos) {
            return (_568_pos).plus(new BigNumber(_567_k));
          })(_565_k));
          return WeakPre.Cond.create_StCond(_566_shiftBy, (c).TrackedVals());
        } else {
          return WeakPre.Cond.create_StFalse();
        }
      } else if (_source37.is_RunOp) {
        let _569___mcc_h48 = (_source37).name;
        let _570___mcc_h49 = (_source37).opcode;
        let _571___mcc_h50 = (_source37).minCapacity;
        let _572___mcc_h51 = (_source37).minOperands;
        let _573___mcc_h52 = (_source37).pushes;
        let _574___mcc_h53 = (_source37).pops;
        let _575_opcode = _570___mcc_h49;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _576_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_577_pos) {
            return (_577_pos).minus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_576_shiftByOne, (c).TrackedVals());
        }
      } else if (_source37.is_StackOp) {
        let _578___mcc_h54 = (_source37).name;
        let _579___mcc_h55 = (_source37).opcode;
        let _580___mcc_h56 = (_source37).minCapacity;
        let _581___mcc_h57 = (_source37).minOperands;
        let _582___mcc_h58 = (_source37).pushes;
        let _583___mcc_h59 = (_source37).pops;
        let _584_opcode = _579___mcc_h55;
        if (((EVMConstants.__default.PUSH0) <= (_584_opcode)) && ((_584_opcode) <= (EVMConstants.__default.PUSH32))) {
          let _source38 = MiscTypes.__default.Find((c).TrackedPos(), _dafny.ZERO);
          if (_source38.is_None) {
            let _585_shiftByMinusOne = MiscTypes.__default.Map((c).TrackedPos(), function (_586_pos) {
              return (_586_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_585_shiftByMinusOne, (c).TrackedVals());
          } else {
            let _587___mcc_h72 = (_source38).v;
            let _588_i = _587___mcc_h72;
            let _589_argVal = Hex.__default.HexToU256(_dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber(64)).minus(new BigNumber(((_this).dtor_arg).length)), function (_590___v142) {
              return new _dafny.CodePoint('0'.codePointAt(0));
            }), (_this).dtor_arg));
            if (_dafny.areEqual((c).TrackedValAt(_588_i), (_589_argVal).Extract())) {
              let _591_filtered = _dafny.Seq.Concat(((c).TrackedPos()).slice(0, _588_i), ((c).TrackedPos()).slice((_588_i).plus(_dafny.ONE)));
              if ((new BigNumber((_591_filtered).length)).isEqualTo(_dafny.ZERO)) {
                return WeakPre.Cond.create_StTrue();
              } else {
                let _592_shiftByMinusOne = MiscTypes.__default.Map(_591_filtered, function (_593_pos) {
                  return (_593_pos).minus(_dafny.ONE);
                });
                return WeakPre.Cond.create_StCond(_592_shiftByMinusOne, _dafny.Seq.Concat(((c).TrackedVals()).slice(0, _588_i), ((c).TrackedVals()).slice((_588_i).plus(_dafny.ONE))));
              }
            } else {
              return WeakPre.Cond.create_StFalse();
            }
          }
        } else if (((EVMConstants.__default.DUP1) <= (_584_opcode)) && ((_584_opcode) <= (EVMConstants.__default.DUP16))) {
          let _source39 = MiscTypes.__default.Find((c).TrackedPos(), _dafny.ZERO);
          if (_source39.is_None) {
            let _594_shiftByMinusOneButZero = MiscTypes.__default.Map((c).TrackedPos(), function (_595_pos) {
              return (_595_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_594_shiftByMinusOneButZero, (c).TrackedVals());
          } else {
            let _596___mcc_h73 = (_source39).v;
            let _597_index0 = _596___mcc_h73;
            let _source40 = MiscTypes.__default.Find((c).TrackedPos(), (new BigNumber((_584_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE));
            if (_source40.is_None) {
              let _598_shiftByMinusOneButZero = MiscTypes.__default.Map((c).TrackedPos(), ((_599_opcode) => function (_600_pos) {
                return (((_600_pos).isEqualTo(_dafny.ZERO)) ? (new BigNumber((_599_opcode) - (EVMConstants.__default.DUP1))) : ((_600_pos).minus(_dafny.ONE)));
              })(_584_opcode));
              return WeakPre.Cond.create_StCond(_598_shiftByMinusOneButZero, (c).TrackedVals());
            } else {
              let _601___mcc_h74 = (_source40).v;
              let _602_index = _601___mcc_h74;
              if (_dafny.areEqual((c).TrackedValAt(_597_index0), (c).TrackedValAt(_602_index))) {
                let _603_filtered = _dafny.Seq.Concat(((c).TrackedPos()).slice(0, _597_index0), ((c).TrackedPos()).slice((_597_index0).plus(_dafny.ONE)));
                let _604_shiftByMinusOne = MiscTypes.__default.Map(_603_filtered, function (_605_pos) {
                  return (_605_pos).minus(_dafny.ONE);
                });
                return WeakPre.Cond.create_StCond(_604_shiftByMinusOne, _dafny.Seq.Concat(((c).TrackedVals()).slice(0, _597_index0), ((c).TrackedVals()).slice((_597_index0).plus(_dafny.ONE))));
              } else {
                return WeakPre.Cond.create_StFalse();
              }
            }
          }
        } else if (((EVMConstants.__default.SWAP1) <= (_584_opcode)) && ((_584_opcode) <= (EVMConstants.__default.SWAP16))) {
          let _606_k = (new BigNumber((_584_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE);
          let _607_swapZeroAndk = MiscTypes.__default.Map((c).TrackedPos(), ((_608_k) => function (_609_pos) {
            return (((_609_pos).isEqualTo(_dafny.ZERO)) ? ((_608_k)) : ((((_609_pos).isEqualTo(_608_k)) ? (_dafny.ZERO) : (_609_pos))));
          })(_606_k));
          return WeakPre.Cond.create_StCond(_607_swapZeroAndk, (c).TrackedVals());
        } else {
          let _610_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_611_i) {
            return (_611_i).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_610_shiftByOne, (c).TrackedVals());
        }
      } else if (_source37.is_LogOp) {
        let _612___mcc_h60 = (_source37).name;
        let _613___mcc_h61 = (_source37).opcode;
        let _614___mcc_h62 = (_source37).minCapacity;
        let _615___mcc_h63 = (_source37).minOperands;
        let _616___mcc_h64 = (_source37).pushes;
        let _617___mcc_h65 = (_source37).pops;
        let _618_pops = _617___mcc_h65;
        let _619_pushes = _616___mcc_h64;
        let _620_opcode = _613___mcc_h61;
        let _621_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_622_pops) => function (_623_pos) {
          return (_623_pos).plus(_622_pops);
        })(_618_pops));
        return WeakPre.Cond.create_StCond(_621_shiftBy, (c).TrackedVals());
      } else {
        let _624___mcc_h66 = (_source37).name;
        let _625___mcc_h67 = (_source37).opcode;
        let _626___mcc_h68 = (_source37).minCapacity;
        let _627___mcc_h69 = (_source37).minOperands;
        let _628___mcc_h70 = (_source37).pushes;
        let _629___mcc_h71 = (_source37).pops;
        let _630_pops = _629___mcc_h71;
        let _631_pushes = _628___mcc_h70;
        let _632_opcode = _625___mcc_h67;
        if ((_631_pushes).isEqualTo(_dafny.ZERO)) {
          let _633_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_634_pops) => function (_635_pos) {
            return (_635_pos).plus(_634_pops);
          })(_630_pops));
          return WeakPre.Cond.create_StCond(_633_shiftBy, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            let _636_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_637_pops) => function (_638_pos) {
              return (_638_pos).plus(_637_pops);
            })(_630_pops));
            return WeakPre.Cond.create_StCond(_636_shiftBy, (c).TrackedVals());
          }
        }
      }
    };
  }
  return $module;
})(); // end of module Instructions
let BinaryDecoder = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "BinaryDecoder._default";
    }
    _parentTraits() {
      return [];
    }
    static Disassemble(s, p, next) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return p;
        } else if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
          return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), s, next)));
        } else {
          let _source41 = Hex.__default.HexToU8((s).slice(0, new BigNumber(2)));
          if (_source41.is_None) {
            return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), (s).slice(0, new BigNumber(2))), _dafny.Seq.UnicodeFromString("' is not a known opcode")), next)));
          } else {
            let _639___mcc_h0 = (_source41).v;
            let _640_v = _639___mcc_h0;
            let _641_op = OpcodeDecoder.__default.Decode(_640_v);
            if ((_dafny.ZERO).isLessThan((_641_op).Args())) {
              if (((new BigNumber(((s).slice(new BigNumber(2))).length)).isLessThan((new BigNumber(2)).multipliedBy((_641_op).Args()))) || (!(BinaryDecoder.__default.IsHexString(((s).slice(new BigNumber(2))).slice(0, (new BigNumber(2)).multipliedBy((_641_op).Args())))))) {
                return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("not enough arguments for opcode "), (_641_op).dtor_name), next)));
              } else {
                let _in25 = ((s).slice(new BigNumber(2))).slice((new BigNumber(2)).multipliedBy((_641_op).Args()));
                let _in26 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_641_op, ((s).slice(new BigNumber(2))).slice(0, (new BigNumber(2)).multipliedBy((_641_op).Args())), next)));
                let _in27 = ((next).plus(_dafny.ONE)).plus((_641_op).Args());
                s = _in25;
                p = _in26;
                next = _in27;
                continue TAIL_CALL_START;
              }
            } else {
              let _in28 = (s).slice(new BigNumber(2));
              let _in29 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_641_op, _dafny.Seq.of(), next)));
              let _in30 = (next).plus(_dafny.ONE);
              s = _in28;
              p = _in29;
              next = _in30;
              continue TAIL_CALL_START;
            }
          }
        }
      }
    };
    static IsHexString(s) {
      return _dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber((s).length)), true, function (_forall_var_3) {
        let _642_k = _forall_var_3;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_642_k)) && ((_642_k).isLessThan(new BigNumber((s).length)))) || (Hex.__default.IsHex((s)[_642_k]));
      });
    };
    static DisassembleU8(s, p, next) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return p;
        } else {
          let _643_op = OpcodeDecoder.__default.Decode((s)[_dafny.ZERO]);
          if ((_dafny.ZERO).isLessThan((_643_op).Args())) {
            if ((new BigNumber(((s).slice(_dafny.ONE)).length)).isLessThan((_643_op).Args())) {
              return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.of(), _dafny.ZERO)));
            } else {
              let _in31 = ((s).slice(_dafny.ONE)).slice((_643_op).Args());
              let _in32 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_643_op, BinaryDecoder.__default.HexHelper(((s).slice(_dafny.ONE)).slice(0, (_643_op).Args())), next)));
              let _in33 = ((next).plus(_dafny.ONE)).plus((_643_op).Args());
              s = _in31;
              p = _in32;
              next = _in33;
              continue TAIL_CALL_START;
            }
          } else {
            let _in34 = (s).slice(_dafny.ONE);
            let _in35 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_643_op, _dafny.Seq.of(), next)));
            let _in36 = (next).plus(_dafny.ONE);
            s = _in34;
            p = _in35;
            next = _in36;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static HexHelper(s) {
      let _644___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_644___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _644___accumulator = _dafny.Seq.Concat(_644___accumulator, Hex.__default.U8ToHex((s)[_dafny.ZERO]));
          let _in37 = (s).slice(_dafny.ONE);
          s = _in37;
          continue TAIL_CALL_START;
        }
      }
    };
    static StringToU8Helper(s, decoded) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Option.create_Some(decoded);
        } else if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
          let _source42 = Hex.__default.HexToU8(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("0"), _dafny.Seq.of((s)[_dafny.ZERO])));
          if (_source42.is_None) {
            return MiscTypes.Option.create_None();
          } else {
            let _645___mcc_h0 = (_source42).v;
            let _646_v = _645___mcc_h0;
            return MiscTypes.Option.create_Some(_dafny.Seq.Concat(decoded, _dafny.Seq.of((_646_v))));
          }
        } else {
          let _source43 = Hex.__default.HexToU8((s).slice(_dafny.ZERO, new BigNumber(2)));
          if (_source43.is_None) {
            return MiscTypes.Option.create_None();
          } else {
            let _647___mcc_h1 = (_source43).v;
            let _648_v = _647___mcc_h1;
            let _in38 = (s).slice(new BigNumber(2));
            let _in39 = _dafny.Seq.Concat(decoded, _dafny.Seq.of((_648_v)));
            s = _in38;
            decoded = _in39;
            continue TAIL_CALL_START;
          }
        }
      }
    };
  };
  return $module;
})(); // end of module BinaryDecoder
let LinSegments = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "LinSegments._default";
    }
    _parentTraits() {
      return [];
    }
    static StackEffectHelper(xs) {
      let _649___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_649___accumulator);
        } else {
          _649___accumulator = (_649___accumulator).plus(((xs)[_dafny.ZERO]).StackEffect());
          let _in40 = (xs).slice(_dafny.ONE);
          xs = _in40;
          continue TAIL_CALL_START;
        }
      }
    };
    static WeakestPreOperandsHelper(xs, postCond) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return postCond;
        } else {
          let _650_lastI = (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
          let _651_e = (_650_lastI).WeakestPreOperands(postCond);
          let _in41 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in42 = _651_e;
          xs = _in41;
          postCond = _in42;
          continue TAIL_CALL_START;
        }
      }
    };
    static WeakestPreCapacityHelper(xs, postCond) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return postCond;
        } else {
          let _652_lastI = (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
          let _653_e = (_652_lastI).WeakestPreCapacity(postCond);
          let _in43 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in44 = _653_e;
          xs = _in43;
          postCond = _in44;
          continue TAIL_CALL_START;
        }
      }
    };
    static RunIns(xs, s) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return s;
        } else {
          let _654_next = ((xs)[_dafny.ZERO]).NextState(s, false);
          let _source44 = _654_next;
          if (_source44.is_EState) {
            let _655___mcc_h0 = (_source44).pc;
            let _656___mcc_h1 = (_source44).stack;
            let _in45 = (xs).slice(_dafny.ONE);
            let _in46 = _654_next;
            xs = _in45;
            s = _in46;
            continue TAIL_CALL_START;
          } else {
            let _657___mcc_h2 = (_source44).msg;
            return _654_next;
          }
        }
      }
    };
    static WPreIns(xs, c) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return c;
        } else if (!((c).is_StCond)) {
          return c;
        } else {
          let _658_c1 = ((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]).WPre(c);
          let _in47 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in48 = _658_c1;
          xs = _in47;
          c = _in48;
          continue TAIL_CALL_START;
        }
      }
    };
    static WPreSeqSegs(path, exits, c, xs, tgtPC) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((path).length)).isEqualTo(_dafny.ZERO)) {
          return c;
        } else {
          let _659_w1 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).WPre(c);
          let _660_wp2 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).LeadsTo(tgtPC, (exits)[(new BigNumber((exits).length)).minus(_dafny.ONE)]);
          let _in49 = (path).slice(0, (new BigNumber((path).length)).minus(_dafny.ONE));
          let _in50 = (exits).slice(0, (new BigNumber((exits).length)).minus(_dafny.ONE));
          let _in51 = (_659_w1).And(_660_wp2);
          let _in52 = xs;
          let _in53 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).StartAddress();
          path = _in49;
          exits = _in50;
          c = _in51;
          xs = _in52;
          tgtPC = _in53;
          continue TAIL_CALL_START;
        }
      }
    };
    static PCToSeg(xs, pc, rank) {
      TAIL_CALL_START: while (true) {
        if ((rank).isEqualTo(new BigNumber((xs).length))) {
          return MiscTypes.Option.create_None();
        } else if ((((xs)[rank]).StartAddress()).isEqualTo(pc)) {
          return MiscTypes.Option.create_Some(rank);
        } else {
          let _in54 = xs;
          let _in55 = pc;
          let _in56 = (rank).plus(_dafny.ONE);
          xs = _in54;
          pc = _in55;
          rank = _in56;
          continue TAIL_CALL_START;
        }
      }
    };
  };

  $module.ValidLinSeg = class ValidLinSeg {
    constructor () {
    }
    static get Witness() {
      return LinSegments.LinSeg.create_CONTSeg(_dafny.Seq.of(), Instructions.Instruction.create_Instruction(EVMOpcodes.Opcode.create_ArithOp(_dafny.Seq.UnicodeFromString("ADD"), EVMConstants.__default.ADD, _dafny.ZERO, new BigNumber(2), _dafny.ONE, new BigNumber(2)), _dafny.Seq.of(), _dafny.ZERO), _dafny.ZERO);
    }
    static get Default() {
      return LinSegments.ValidLinSeg.Witness;
    }
  };

  $module.LinSeg = class LinSeg {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JUMPSeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(0);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    static create_JUMPISeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(1);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    static create_RETURNSeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(2);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    static create_STOPSeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(3);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    static create_CONTSeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(4);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    static create_INVALIDSeg(ins, lastIns, netOpEffect) {
      let $dt = new LinSeg(5);
      $dt.ins = ins;
      $dt.lastIns = lastIns;
      $dt.netOpEffect = netOpEffect;
      return $dt;
    }
    get is_JUMPSeg() { return this.$tag === 0; }
    get is_JUMPISeg() { return this.$tag === 1; }
    get is_RETURNSeg() { return this.$tag === 2; }
    get is_STOPSeg() { return this.$tag === 3; }
    get is_CONTSeg() { return this.$tag === 4; }
    get is_INVALIDSeg() { return this.$tag === 5; }
    get dtor_ins() { return this.ins; }
    get dtor_lastIns() { return this.lastIns; }
    get dtor_netOpEffect() { return this.netOpEffect; }
    toString() {
      if (this.$tag === 0) {
        return "LinSegments.LinSeg.JUMPSeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else if (this.$tag === 1) {
        return "LinSegments.LinSeg.JUMPISeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else if (this.$tag === 2) {
        return "LinSegments.LinSeg.RETURNSeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else if (this.$tag === 3) {
        return "LinSegments.LinSeg.STOPSeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else if (this.$tag === 4) {
        return "LinSegments.LinSeg.CONTSeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else if (this.$tag === 5) {
        return "LinSegments.LinSeg.INVALIDSeg" + "(" + _dafny.toString(this.ins) + ", " + _dafny.toString(this.lastIns) + ", " + _dafny.toString(this.netOpEffect) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else if (this.$tag === 5) {
        return other.$tag === 5 && _dafny.areEqual(this.ins, other.ins) && _dafny.areEqual(this.lastIns, other.lastIns) && _dafny.areEqual(this.netOpEffect, other.netOpEffect);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return LinSegments.LinSeg.create_JUMPSeg(_dafny.Seq.of(), Instructions.ValidInstruction.Default, _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return LinSeg.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      let _source45 = _this;
      if (_source45.is_JUMPSeg) {
        let _661___mcc_h0 = (_source45).ins;
        let _662___mcc_h1 = (_source45).lastIns;
        let _663___mcc_h2 = (_source45).netOpEffect;
        return ((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMP);
      } else if (_source45.is_JUMPISeg) {
        let _664___mcc_h3 = (_source45).ins;
        let _665___mcc_h4 = (_source45).lastIns;
        let _666___mcc_h5 = (_source45).netOpEffect;
        return ((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPI);
      } else if (_source45.is_RETURNSeg) {
        let _667___mcc_h6 = (_source45).ins;
        let _668___mcc_h7 = (_source45).lastIns;
        let _669___mcc_h8 = (_source45).netOpEffect;
        return ((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.RETURN);
      } else if (_source45.is_STOPSeg) {
        let _670___mcc_h9 = (_source45).ins;
        let _671___mcc_h10 = (_source45).lastIns;
        let _672___mcc_h11 = (_source45).netOpEffect;
        return (((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.STOP)) || (((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.REVERT));
      } else if (_source45.is_CONTSeg) {
        let _673___mcc_h12 = (_source45).ins;
        let _674___mcc_h13 = (_source45).lastIns;
        let _675___mcc_h14 = (_source45).netOpEffect;
        return ((((_this).dtor_lastIns).dtor_op).dtor_opcode) !== (EVMConstants.__default.INVALID);
      } else {
        let _676___mcc_h15 = (_source45).ins;
        let _677___mcc_h16 = (_source45).lastIns;
        let _678___mcc_h17 = (_source45).netOpEffect;
        return ((((_this).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID);
      }
    };
    Ins() {
      let _this = this;
      return _dafny.Seq.Concat((_this).dtor_ins, _dafny.Seq.of((_this).dtor_lastIns));
    };
    StartAddress() {
      let _this = this;
      return (((_this).Ins())[_dafny.ZERO]).dtor_address;
    };
    NetOpEffect() {
      let _this = this;
      return (_this).dtor_netOpEffect;
    };
    NetCapEffect() {
      let _this = this;
      return (_dafny.ZERO).minus((_this).dtor_netOpEffect);
    };
    StackEffect() {
      let _this = this;
      return (_this).dtor_netOpEffect;
    };
    StartAddressNextSeg() {
      let _this = this;
      return ((((_this).dtor_lastIns).dtor_address).plus(_dafny.ONE)).plus(_dafny.EuclideanDivision(new BigNumber((((_this).dtor_lastIns).dtor_arg).length), new BigNumber(2)));
    };
    CollectJumpDest(rest) {
      let _this = this;
      let _679___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((rest).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_679___accumulator, _dafny.Seq.of());
        } else if (((((rest)[_dafny.ZERO]).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPDEST)) {
          _679___accumulator = _dafny.Seq.Concat(_679___accumulator, _dafny.Seq.of(((rest)[_dafny.ZERO]).dtor_address));
          let _in57 = _this;
          let _in58 = (rest).slice(_dafny.ONE);
          _this = _in57;
          ;
          rest = _in58;
          continue TAIL_CALL_START;
        } else {
          let _in59 = _this;
          let _in60 = (rest).slice(_dafny.ONE);
          _this = _in59;
          ;
          rest = _in60;
          continue TAIL_CALL_START;
        }
      }
    };
    WeakestPreOperands(n) {
      let _this = this;
      return LinSegments.__default.WeakestPreOperandsHelper((_this).Ins(), n);
    };
    WeakestPreCapacity(n) {
      let _this = this;
      return LinSegments.__default.WeakestPreCapacityHelper((_this).Ins(), n);
    };
    Run(s, exit) {
      let _this = this;
      let _680_s_k = LinSegments.__default.RunIns((_this).dtor_ins, s);
      if ((_680_s_k).is_Error) {
        return _680_s_k;
      } else {
        return ((_this).dtor_lastIns).NextState(_680_s_k, exit);
      }
    };
    WPre(c) {
      let _this = this;
      return LinSegments.__default.WPreIns((_this).Ins(), c);
    };
    HasExit(b) {
      let _this = this;
      let _source46 = _this;
      if (_source46.is_JUMPSeg) {
        let _681___mcc_h0 = (_source46).ins;
        let _682___mcc_h1 = (_source46).lastIns;
        let _683___mcc_h2 = (_source46).netOpEffect;
        return b;
      } else if (_source46.is_JUMPISeg) {
        let _684___mcc_h6 = (_source46).ins;
        let _685___mcc_h7 = (_source46).lastIns;
        let _686___mcc_h8 = (_source46).netOpEffect;
        return true;
      } else if (_source46.is_RETURNSeg) {
        let _687___mcc_h12 = (_source46).ins;
        let _688___mcc_h13 = (_source46).lastIns;
        let _689___mcc_h14 = (_source46).netOpEffect;
        return false;
      } else if (_source46.is_STOPSeg) {
        let _690___mcc_h18 = (_source46).ins;
        let _691___mcc_h19 = (_source46).lastIns;
        let _692___mcc_h20 = (_source46).netOpEffect;
        return false;
      } else if (_source46.is_CONTSeg) {
        let _693___mcc_h24 = (_source46).ins;
        let _694___mcc_h25 = (_source46).lastIns;
        let _695___mcc_h26 = (_source46).netOpEffect;
        return !(b);
      } else {
        let _696___mcc_h30 = (_source46).ins;
        let _697___mcc_h31 = (_source46).lastIns;
        let _698___mcc_h32 = (_source46).netOpEffect;
        return false;
      }
    };
    LeadsTo(k, exit) {
      let _this = this;
      if ((Int.__default.TWO__256).isLessThanOrEqualTo(k)) {
        return WeakPre.Cond.create_StFalse();
      } else {
        let _source47 = _this;
        if (_source47.is_JUMPSeg) {
          let _699___mcc_h0 = (_source47).ins;
          let _700___mcc_h1 = (_source47).lastIns;
          let _701___mcc_h2 = (_source47).netOpEffect;
          if (exit) {
            let _702_c = WeakPre.Cond.create_StCond(_dafny.Seq.of(_dafny.ZERO), _dafny.Seq.of(k));
            return LinSegments.__default.WPreIns((_this).dtor_ins, _702_c);
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else if (_source47.is_JUMPISeg) {
          let _703___mcc_h3 = (_source47).ins;
          let _704___mcc_h4 = (_source47).lastIns;
          let _705___mcc_h5 = (_source47).netOpEffect;
          if (exit) {
            let _706_c = WeakPre.Cond.create_StCond(_dafny.Seq.of(_dafny.ZERO), _dafny.Seq.of(k));
            return LinSegments.__default.WPreIns((_this).dtor_ins, _706_c);
          } else if ((k).isEqualTo((_this).StartAddressNextSeg())) {
            return WeakPre.Cond.create_StTrue();
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else if (_source47.is_RETURNSeg) {
          let _707___mcc_h6 = (_source47).ins;
          let _708___mcc_h7 = (_source47).lastIns;
          let _709___mcc_h8 = (_source47).netOpEffect;
          return WeakPre.Cond.create_StTrue();
        } else if (_source47.is_STOPSeg) {
          let _710___mcc_h9 = (_source47).ins;
          let _711___mcc_h10 = (_source47).lastIns;
          let _712___mcc_h11 = (_source47).netOpEffect;
          return WeakPre.Cond.create_StTrue();
        } else if (_source47.is_CONTSeg) {
          let _713___mcc_h12 = (_source47).ins;
          let _714___mcc_h13 = (_source47).lastIns;
          let _715___mcc_h14 = (_source47).netOpEffect;
          if ((!(exit)) && ((k).isEqualTo((_this).StartAddressNextSeg()))) {
            return WeakPre.Cond.create_StTrue();
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else {
          let _716___mcc_h15 = (_source47).ins;
          let _717___mcc_h16 = (_source47).lastIns;
          let _718___mcc_h17 = (_source47).netOpEffect;
          return WeakPre.Cond.create_StFalse();
        }
      }
    };
  }
  return $module;
})(); // end of module LinSegments
let Splitter = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Splitter._default";
    }
    _parentTraits() {
      return [];
    }
    static BuildSeg(xs, lastInst) {
      if ((((lastInst).dtor_op).dtor_opcode) === (86)) {
        return LinSegments.LinSeg.create_JUMPSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(_dafny.Seq.Concat(xs, _dafny.Seq.of(lastInst)), _dafny.ZERO));
      } else if ((((lastInst).dtor_op).dtor_opcode) === (87)) {
        return LinSegments.LinSeg.create_JUMPISeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(_dafny.Seq.Concat(xs, _dafny.Seq.of(lastInst)), _dafny.ZERO));
      } else if ((((lastInst).dtor_op).dtor_opcode) === (243)) {
        return LinSegments.LinSeg.create_RETURNSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(xs, _dafny.ZERO));
      } else if ((((lastInst).dtor_op).dtor_opcode) === (253)) {
        return LinSegments.LinSeg.create_STOPSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(xs, _dafny.ZERO));
      } else if ((((lastInst).dtor_op).dtor_opcode) === (0)) {
        return LinSegments.LinSeg.create_STOPSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(xs, _dafny.ZERO));
      } else if ((((lastInst).dtor_op).dtor_opcode) === (254)) {
        return LinSegments.LinSeg.create_INVALIDSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(xs, _dafny.ZERO));
      } else {
        return LinSegments.LinSeg.create_CONTSeg(xs, lastInst, Splitter.__default.DeltaOperandsHelper(_dafny.Seq.Concat(xs, _dafny.Seq.of(lastInst)), _dafny.ZERO));
      }
    };
    static EndOfSegment(xs) {
      if (((xs)[_dafny.ZERO]).IsTerminal()) {
        return true;
      } else if (((_dafny.ONE).isLessThan(new BigNumber((xs).length))) && (((xs)[_dafny.ONE]).IsJumpDest())) {
        return true;
      } else {
        return false;
      }
    };
    static SplitUpToTerminal(xs, curseq, collected) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return collected;
        } else if ((new BigNumber((xs).length)).isEqualTo(_dafny.ONE)) {
          return _dafny.Seq.Concat(collected, _dafny.Seq.of(Splitter.__default.BuildSeg(curseq, (xs)[_dafny.ZERO])));
        } else if (Splitter.__default.EndOfSegment(xs)) {
          let _719_newSeg = _dafny.Seq.Concat(curseq, _dafny.Seq.of((xs)[_dafny.ZERO]));
          let _in61 = (xs).slice(_dafny.ONE);
          let _in62 = _dafny.Seq.of();
          let _in63 = _dafny.Seq.Concat(collected, _dafny.Seq.of(Splitter.__default.BuildSeg(curseq, (xs)[_dafny.ZERO])));
          xs = _in61;
          curseq = _in62;
          collected = _in63;
          continue TAIL_CALL_START;
        } else {
          let _in64 = (xs).slice(_dafny.ONE);
          let _in65 = _dafny.Seq.Concat(curseq, _dafny.Seq.of((xs)[_dafny.ZERO]));
          let _in66 = collected;
          xs = _in64;
          curseq = _in65;
          collected = _in66;
          continue TAIL_CALL_START;
        }
      }
    };
    static DeltaOperandsHelper(xs, current) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return current;
        } else {
          let _720_e = (current).plus(((((xs)[_dafny.ZERO]).dtor_op).dtor_pushes).minus((((xs)[_dafny.ZERO]).dtor_op).dtor_pops));
          let _in67 = (xs).slice(_dafny.ONE);
          let _in68 = _720_e;
          xs = _in67;
          current = _in68;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Splitter
let SegBuilder = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "SegBuilder._default";
    }
    _parentTraits() {
      return [];
    }
    static JUMPResolver(s) {
      return SegBuilder.__default.StackPositionTracker((s).dtor_ins, _dafny.ZERO);
    };
    static StackPositionTracker(xs, pos) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right(pos);
        } else {
          let _721_x = ((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]).StackPosBackWardTracker(pos);
          let _source48 = _721_x;
          if (_source48.is_Left) {
            let _722___mcc_h0 = (_source48).l;
            let _723_v = _722___mcc_h0;
            return MiscTypes.Either.create_Left(_723_v);
          } else {
            let _724___mcc_h1 = (_source48).r;
            let _725_v = _724___mcc_h1;
            let _in69 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
            let _in70 = _725_v;
            xs = _in69;
            pos = _in70;
            continue TAIL_CALL_START;
          }
        }
      }
    };
  };
  return $module;
})(); // end of module SegBuilder
let ProofObject = (function() {
  let $module = {};


  $module.StackResolver = class StackResolver {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_StackResolver(sp) {
      let $dt = new StackResolver(0);
      $dt.sp = sp;
      return $dt;
    }
    get is_StackResolver() { return this.$tag === 0; }
    get dtor_sp() { return this.sp; }
    toString() {
      if (this.$tag === 0) {
        return "ProofObject.StackResolver.StackResolver" + "(" + _dafny.toString(this.sp) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.sp, other.sp);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return _dafny.Map.Empty;
    }
    static Rtd() {
      return class {
        static get Default() {
          return StackResolver.Default();
        }
      };
    }
  }

  $module.ProofObj = class ProofObj {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_JUMP(s, wpOp, wpCap, tgt, stacks) {
      let $dt = new ProofObj(0);
      $dt.s = s;
      $dt.wpOp = wpOp;
      $dt.wpCap = wpCap;
      $dt.tgt = tgt;
      $dt.stacks = stacks;
      return $dt;
    }
    static create_CONT(s, wpOp, wpCap, stacks) {
      let $dt = new ProofObj(1);
      $dt.s = s;
      $dt.wpOp = wpOp;
      $dt.wpCap = wpCap;
      $dt.stacks = stacks;
      return $dt;
    }
    static create_TERMINAL(s, wpOp, wpCap, stacks) {
      let $dt = new ProofObj(2);
      $dt.s = s;
      $dt.wpOp = wpOp;
      $dt.wpCap = wpCap;
      $dt.stacks = stacks;
      return $dt;
    }
    get is_JUMP() { return this.$tag === 0; }
    get is_CONT() { return this.$tag === 1; }
    get is_TERMINAL() { return this.$tag === 2; }
    get dtor_s() { return this.s; }
    get dtor_wpOp() { return this.wpOp; }
    get dtor_wpCap() { return this.wpCap; }
    get dtor_tgt() { return this.tgt; }
    get dtor_stacks() { return this.stacks; }
    toString() {
      if (this.$tag === 0) {
        return "ProofObject.ProofObj.JUMP" + "(" + _dafny.toString(this.s) + ", " + _dafny.toString(this.wpOp) + ", " + _dafny.toString(this.wpCap) + ", " + _dafny.toString(this.tgt) + ", " + _dafny.toString(this.stacks) + ")";
      } else if (this.$tag === 1) {
        return "ProofObject.ProofObj.CONT" + "(" + _dafny.toString(this.s) + ", " + _dafny.toString(this.wpOp) + ", " + _dafny.toString(this.wpCap) + ", " + _dafny.toString(this.stacks) + ")";
      } else if (this.$tag === 2) {
        return "ProofObject.ProofObj.TERMINAL" + "(" + _dafny.toString(this.s) + ", " + _dafny.toString(this.wpOp) + ", " + _dafny.toString(this.wpCap) + ", " + _dafny.toString(this.stacks) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.s, other.s) && _dafny.areEqual(this.wpOp, other.wpOp) && _dafny.areEqual(this.wpCap, other.wpCap) && _dafny.areEqual(this.tgt, other.tgt) && _dafny.areEqual(this.stacks, other.stacks);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.s, other.s) && _dafny.areEqual(this.wpOp, other.wpOp) && _dafny.areEqual(this.wpCap, other.wpCap) && _dafny.areEqual(this.stacks, other.stacks);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.s, other.s) && _dafny.areEqual(this.wpOp, other.wpOp) && _dafny.areEqual(this.wpCap, other.wpCap) && _dafny.areEqual(this.stacks, other.stacks);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProofObject.ProofObj.create_JUMP(LinSegments.ValidLinSeg.Default, _dafny.ZERO, _dafny.ZERO, MiscTypes.Either.Default(StackElement.StackElem.Default()), _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return ProofObj.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      let _source49 = _this;
      if (_source49.is_JUMP) {
        let _726___mcc_h0 = (_source49).s;
        let _727___mcc_h1 = (_source49).wpOp;
        let _728___mcc_h2 = (_source49).wpCap;
        let _729___mcc_h3 = (_source49).tgt;
        let _730___mcc_h4 = (_source49).stacks;
        return (((_this).dtor_s).is_JUMPSeg) || (((_this).dtor_s).is_JUMPISeg);
      } else if (_source49.is_CONT) {
        let _731___mcc_h5 = (_source49).s;
        let _732___mcc_h6 = (_source49).wpOp;
        let _733___mcc_h7 = (_source49).wpCap;
        let _734___mcc_h8 = (_source49).stacks;
        return ((_this).dtor_s).is_CONTSeg;
      } else {
        let _735___mcc_h9 = (_source49).s;
        let _736___mcc_h10 = (_source49).wpOp;
        let _737___mcc_h11 = (_source49).wpCap;
        let _738___mcc_h12 = (_source49).stacks;
        return ((((_this).dtor_s).is_RETURNSeg) || (((_this).dtor_s).is_STOPSeg)) || (((_this).dtor_s).is_INVALIDSeg);
      }
    };
    CollectJumpDest() {
      let _this = this;
      return ((_this).dtor_s).CollectJumpDest(((_this).dtor_s).Ins());
    };
    StackEffect() {
      let _this = this;
      return ((_this).dtor_s).StackEffect();
    };
  }
  return $module;
})(); // end of module ProofObject
let PrettyIns = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "PrettyIns._default";
    }
    _parentTraits() {
      return [];
    }
    static PrintInstructionToDafny(i, src, tgt) {
      if ((((i).dtor_op).dtor_opcode) === (1)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Add(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (2)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Mul(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (3)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Sub(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (4)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Div(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (5)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := SDiv(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (6)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Mod(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (7)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := SMod(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (8)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := AddMod(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (9)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := MulMod(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (10)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Exp(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (11)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := SignExtended(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (16)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Bytecode.Lt(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (80)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Pop(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (82)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Bytecode.MStore(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (86)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Jump(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (87)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := JumpI(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (91)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := JumpDest(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (95)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Push0(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (96)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Push1(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 0x")), (i).dtor_arg), _dafny.Seq.UnicodeFromString(");"));
      } else if ((((i).dtor_op).dtor_opcode) === (128)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 1);"));
      } else if ((((i).dtor_op).dtor_opcode) === (129)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 2);"));
      } else if ((((i).dtor_op).dtor_opcode) === (130)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 3);"));
      } else if ((((i).dtor_op).dtor_opcode) === (131)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 4);"));
      } else if ((((i).dtor_op).dtor_opcode) === (132)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 5);"));
      } else if ((((i).dtor_op).dtor_opcode) === (133)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 6);"));
      } else if ((((i).dtor_op).dtor_opcode) === (134)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 7);"));
      } else if ((((i).dtor_op).dtor_opcode) === (135)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 8);"));
      } else if ((((i).dtor_op).dtor_opcode) === (136)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 9);"));
      } else if ((((i).dtor_op).dtor_opcode) === (137)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 10);"));
      } else if ((((i).dtor_op).dtor_opcode) === (138)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 11);"));
      } else if ((((i).dtor_op).dtor_opcode) === (139)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 12);"));
      } else if ((((i).dtor_op).dtor_opcode) === (140)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 13);"));
      } else if ((((i).dtor_op).dtor_opcode) === (141)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 14);"));
      } else if ((((i).dtor_op).dtor_opcode) === (142)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 15);"));
      } else if ((((i).dtor_op).dtor_opcode) === (143)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Dup(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 16);"));
      } else if ((((i).dtor_op).dtor_opcode) === (144)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 1);"));
      } else if ((((i).dtor_op).dtor_opcode) === (145)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 2);"));
      } else if ((((i).dtor_op).dtor_opcode) === (146)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 3);"));
      } else if ((((i).dtor_op).dtor_opcode) === (147)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 4);"));
      } else if ((((i).dtor_op).dtor_opcode) === (148)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 5);"));
      } else if ((((i).dtor_op).dtor_opcode) === (149)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 6);"));
      } else if ((((i).dtor_op).dtor_opcode) === (150)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 7);"));
      } else if ((((i).dtor_op).dtor_opcode) === (151)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 8);"));
      } else if ((((i).dtor_op).dtor_opcode) === (152)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 9);"));
      } else if ((((i).dtor_op).dtor_opcode) === (153)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 10);"));
      } else if ((((i).dtor_op).dtor_opcode) === (154)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 11);"));
      } else if ((((i).dtor_op).dtor_opcode) === (155)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 12);"));
      } else if ((((i).dtor_op).dtor_opcode) === (156)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 13);"));
      } else if ((((i).dtor_op).dtor_opcode) === (157)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 14);"));
      } else if ((((i).dtor_op).dtor_opcode) === (158)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 15);"));
      } else if ((((i).dtor_op).dtor_opcode) === (159)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Swap(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(", 16);"));
      } else if ((((i).dtor_op).dtor_opcode) === (243)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("var s"), PrettyIns.__default.DecToString(tgt)), _dafny.Seq.UnicodeFromString(" := Return(s")), PrettyIns.__default.DecToString(src)), _dafny.Seq.UnicodeFromString(");"));
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Unknwon instruction:"), ((i).dtor_op).dtor_name);
      }
    };
    static DecToChar(n) {
      if ((n).isEqualTo(_dafny.ZERO)) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      } else if ((n).isEqualTo(_dafny.ONE)) {
        return new _dafny.CodePoint('1'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(2))) {
        return new _dafny.CodePoint('2'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(3))) {
        return new _dafny.CodePoint('3'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(4))) {
        return new _dafny.CodePoint('4'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(5))) {
        return new _dafny.CodePoint('5'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(6))) {
        return new _dafny.CodePoint('6'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(7))) {
        return new _dafny.CodePoint('7'.codePointAt(0));
      } else if ((n).isEqualTo(new BigNumber(8))) {
        return new _dafny.CodePoint('8'.codePointAt(0));
      } else {
        return new _dafny.CodePoint('9'.codePointAt(0));
      }
    };
    static DecToString(n) {
      let _739___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(10))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(PrettyIns.__default.DecToChar(n)), _739___accumulator);
        } else {
          _739___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(PrettyIns.__default.DecToChar((n).mod(new BigNumber(10)))), _739___accumulator);
          let _in71 = _dafny.EuclideanDivision(n, new BigNumber(10));
          n = _in71;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module PrettyIns
let PrettyPrinters = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "PrettyPrinters._default";
    }
    _parentTraits() {
      return [];
    }
    static PrintInstructions(s) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((s).length))) {
          let _740_formattedAddress;
          _740_formattedAddress = (((((s)[_dafny.ZERO]).dtor_address).isLessThan(Int.__default.TWO__32)) ? (Hex.__default.U32ToHex((((s)[_dafny.ZERO]).dtor_address).toNumber())) : (_dafny.Seq.UnicodeFromString("OutofRange")));
          process.stdout.write((_740_formattedAddress).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(": ")).toVerbatimString(false));
          process.stdout.write((((s)[_dafny.ZERO]).ToString()).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _in72 = (s).slice(_dafny.ONE);
          s = _in72;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static PrintSegments(xs, num) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xs).length))) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("Segment ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(num));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _741_k;
          _741_k = ((xs)[_dafny.ZERO]).WeakestPreOperands(_dafny.ZERO);
          let _742_l;
          _742_l = ((xs)[_dafny.ZERO]).WeakestPreCapacity(_dafny.ZERO);
          if ((((xs)[_dafny.ZERO]).is_JUMPSeg) || (((xs)[_dafny.ZERO]).is_JUMPISeg)) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("JUMP/JUMPI: tgt address at the end: ")).toVerbatimString(false));
            let _743_r;
            _743_r = SegBuilder.__default.JUMPResolver((xs)[_dafny.ZERO]);
            let _source50 = _743_r;
            if (_source50.is_Left) {
              let _744___mcc_h0 = (_source50).l;
              let _745_v = _744___mcc_h0;
              let _source51 = _745_v;
              if (_source51.is_Value) {
                let _746___mcc_h2 = (_source51).v;
                let _747_address = _746___mcc_h2;
                process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("0x"), Hex.__default.NatToHex(_747_address))).toVerbatimString(false));
              } else {
                let _748___mcc_h3 = (_source51).s;
                let _749_msg = _748___mcc_h3;
                process.stdout.write((_dafny.Seq.UnicodeFromString("Could not determine stack value")).toVerbatimString(false));
              }
            } else {
              let _750___mcc_h1 = (_source50).r;
              let _751_stackPos = _750___mcc_h1;
              process.stdout.write((_dafny.Seq.UnicodeFromString("Peek(")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_751_stackPos));
              process.stdout.write((_dafny.Seq.UnicodeFromString(")")).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          }
          if (((xs)[_dafny.ZERO]).is_CONTSeg) {
            if ((((((xs)[_dafny.ZERO]).dtor_lastIns).dtor_op).dtor_opcode) !== (EVMConstants.__default.INVALID)) {
              let _752_nextPC;
              _752_nextPC = ((xs)[_dafny.ZERO]).StartAddressNextSeg();
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("CONT: PC of instruction after last is: "), _dafny.Seq.UnicodeFromString(" 0x")), Hex.__default.NatToHex(_752_nextPC)), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
            } else {
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("CONT: has an invaid instructiom"), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("WeakestPre Operands:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(_741_k));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("WeakestPre Capacity:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(_742_l));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("Net Stack Effect:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(((xs)[_dafny.ZERO]).StackEffect()));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          }
          PrettyPrinters.__default.PrintInstructions(((xs)[_dafny.ZERO]).Ins());
          let _in73 = (xs).slice(_dafny.ONE);
          let _in74 = (num).plus(_dafny.ONE);
          xs = _in73;
          num = _in74;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static CollectJumpDest(xs) {
      let _753___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_753___accumulator, _dafny.Seq.of());
        } else {
          _753___accumulator = _dafny.Seq.Concat(_753___accumulator, ((xs)[_dafny.ZERO]).CollectJumpDest());
          let _in75 = (xs).slice(_dafny.ONE);
          xs = _in75;
          continue TAIL_CALL_START;
        }
      }
    };
    static CollectJumpDestAsString(xs) {
      let _754___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_754___accumulator, _dafny.Seq.of());
        } else {
          _754___accumulator = _dafny.Seq.Concat(_754___accumulator, _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" ensures s.IsJumpDest(0x"), Hex.__default.NatToHex((xs)[_dafny.ZERO])), _dafny.Seq.UnicodeFromString(" as u256)\n")));
          let _in76 = (xs).slice(_dafny.ONE);
          xs = _in76;
          continue TAIL_CALL_START;
        }
      }
    };
    static PrintProofObjectToDafny(xs, pathToEVMDafny) {
      if ((_dafny.ZERO).isLessThan(new BigNumber((pathToEVMDafny).length))) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("include \"")).toVerbatimString(false));
        process.stdout.write((pathToEVMDafny).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("/src/dafny/state.dfy\"")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("include \"")).toVerbatimString(false));
        process.stdout.write((pathToEVMDafny).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("/src/dafny/bytecode.dfy\"")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      process.stdout.write((_dafny.Seq.UnicodeFromString("module DafnyEVMProofObject {")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("import opened Int")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("import EvmState")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("import opened Bytecode")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      let _755_j;
      _755_j = PrettyPrinters.__default.CollectJumpDestAsString(PrettyPrinters.__default.CollectJumpDest(xs));
      if ((_dafny.ZERO).isLessThan(new BigNumber((_755_j).length))) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("/** Lemma for Jumpdest */")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_755_j).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      PrettyPrinters.__default.PrintProofObjectBody(xs, _dafny.ZERO);
      process.stdout.write((_dafny.Seq.UnicodeFromString("}")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
    static PrintProofObjectBody(xs, num) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xs).length))) {
          let _756_startAddress;
          _756_startAddress = Hex.__default.NatToHex((((((xs)[_dafny.ZERO]).dtor_s).Ins())[_dafny.ZERO]).dtor_address);
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n/** Code starting at 0x")).toVerbatimString(false));
          process.stdout.write((_756_startAddress).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(" */\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("function {:opaque} ExecuteFromTag_")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(num));
          process.stdout.write((_dafny.Seq.UnicodeFromString("(s0: EvmState.ExecutingState): (s': EvmState.State)\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.PC() == 0x")).toVerbatimString(false));
          process.stdout.write((_756_startAddress).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(" as nat\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  // Net Operands effect ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString((((xs)[_dafny.ZERO]).dtor_s).NetOpEffect()));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.Operands() >= ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(((xs)[_dafny.ZERO]).dtor_wpOp));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  // Net Capacity effect ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString((((xs)[_dafny.ZERO]).dtor_s).NetCapEffect()));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.Capacity() >= ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(((xs)[_dafny.ZERO]).dtor_wpCap));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          if ((((xs)[_dafny.ZERO]).is_JUMP) && ((((((xs)[_dafny.ZERO]).dtor_s).dtor_lastIns).dtor_op).IsJump())) {
            {
              let _source52 = ((xs)[_dafny.ZERO]).dtor_tgt;
              if (_source52.is_Left) {
                let _757___mcc_h0 = (_source52).l;
                process.stdout.write((_dafny.Seq.UnicodeFromString("")).toVerbatimString(false));
              } else {
                let _758___mcc_h2 = (_source52).r;
                let _759_v = _758___mcc_h2;
                process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.IsJumpDest(s0.Peek(")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_759_v));
                process.stdout.write((_dafny.Seq.UnicodeFromString("))\n")).toVerbatimString(false));
              }
            }
          }
          let _source53 = (xs)[_dafny.ZERO];
          if (_source53.is_JUMP) {
            let _760___mcc_h4 = (_source53).s;
            let _761___mcc_h5 = (_source53).wpOp;
            let _762___mcc_h6 = (_source53).wpCap;
            let _763___mcc_h7 = (_source53).tgt;
            let _764___mcc_h8 = (_source53).stacks;
            let _765_tgt = _763___mcc_h7;
            let _766_s = _760___mcc_h4;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.EXECUTING?\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.PC() ==  ")).toVerbatimString(false));
            {
              let _source54 = _765_tgt;
              if (_source54.is_Left) {
                let _767___mcc_h17 = (_source54).l;
                let _768_xc = _767___mcc_h17;
                let _source55 = _768_xc;
                if (_source55.is_Value) {
                  let _769___mcc_h19 = (_source55).v;
                  let _770_v = _769___mcc_h19;
                  process.stdout.write((_dafny.Seq.UnicodeFromString("0x")).toVerbatimString(false));
                  process.stdout.write((Hex.__default.NatToHex((_768_xc).Extract())).toVerbatimString(false));
                } else {
                  let _771___mcc_h21 = (_source55).s;
                  process.stdout.write((_dafny.Seq.UnicodeFromString("Could not extract value ")).toVerbatimString(false));
                }
              } else {
                let _772___mcc_h18 = (_source54).r;
                let _773_v = _772___mcc_h18;
                process.stdout.write((_dafny.Seq.UnicodeFromString("s0.Peek(")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_773_v));
                process.stdout.write((_dafny.Seq.UnicodeFromString(") as nat")).toVerbatimString(false));
              }
            }
            if (((((_766_s).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPI)) {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" || s'.PC() == 0x")).toVerbatimString(false));
              process.stdout.write((Hex.__default.NatToHex((((_766_s).dtor_lastIns).dtor_address).plus(_dafny.ONE))).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            let _774_n;
            _774_n = ((xs)[_dafny.ZERO]).StackEffect();
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.Operands() == s0.Operands()")).toVerbatimString(false));
            if ((_dafny.ZERO).isLessThanOrEqualTo(_774_n)) {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" + ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_774_n));
            } else {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" - ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_dafny.ZERO).minus(_774_n)));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          } else if (_source53.is_CONT) {
            let _775___mcc_h9 = (_source53).s;
            let _776___mcc_h10 = (_source53).wpOp;
            let _777___mcc_h11 = (_source53).wpCap;
            let _778___mcc_h12 = (_source53).stacks;
            let _779_s = _775___mcc_h9;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.EXECUTING?\n")).toVerbatimString(false));
            if (((((_779_s).dtor_lastIns).dtor_op).dtor_opcode) !== (EVMConstants.__default.INVALID)) {
              let _780_nextPC;
              _780_nextPC = (_779_s).StartAddressNextSeg();
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("  ensures s'.PC() == 0x"), Hex.__default.NatToHex(_780_nextPC)), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
              let _781_n;
              _781_n = ((xs)[_dafny.ZERO]).StackEffect();
              process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.Operands() == s0.Operands()")).toVerbatimString(false));
              if ((_dafny.ZERO).isLessThanOrEqualTo(_781_n)) {
                process.stdout.write((_dafny.Seq.UnicodeFromString(" + ")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_781_n));
              } else {
                process.stdout.write((_dafny.Seq.UnicodeFromString(" - ")).toVerbatimString(false));
                process.stdout.write(_dafny.toString((_dafny.ZERO).minus(_781_n)));
              }
            } else {
              process.stdout.write((_dafny.Seq.UnicodeFromString("  Last instruction is invalid")).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          } else {
            let _782___mcc_h13 = (_source53).s;
            let _783___mcc_h14 = (_source53).wpOp;
            let _784___mcc_h15 = (_source53).wpCap;
            let _785___mcc_h16 = (_source53).stacks;
            let _786_s = _782___mcc_h13;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.RETURNS?\n")).toVerbatimString(false));
          }
          process.stdout.write((_dafny.Seq.UnicodeFromString("{\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  ValidJumpDest(s0);\n")).toVerbatimString(false));
          PrettyPrinters.__default.PrintInstructionsToDafny((((xs)[_dafny.ZERO]).dtor_s).Ins(), _dafny.ZERO);
          process.stdout.write((_dafny.Seq.UnicodeFromString("  s")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(new BigNumber(((((xs)[_dafny.ZERO]).dtor_s).Ins()).length)));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("}\n")).toVerbatimString(false));
          let _in77 = (xs).slice(_dafny.ONE);
          let _in78 = (num).plus(_dafny.ONE);
          xs = _in77;
          num = _in78;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static PrintInstructionsToDafny(xs, pos) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xs).length))) {
          let _787_k;
          _787_k = PrettyIns.__default.PrintInstructionToDafny((xs)[_dafny.ZERO], pos, (pos).plus(_dafny.ONE));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  ")).toVerbatimString(false));
          process.stdout.write((_787_k).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _in79 = (xs).slice(_dafny.ONE);
          let _in80 = (pos).plus(_dafny.ONE);
          xs = _in79;
          pos = _in80;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
  };
  return $module;
})(); // end of module PrettyPrinters
let ProofObjectBuilder = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "ProofObjectBuilder._default";
    }
    _parentTraits() {
      return [];
    }
    static BuildProofObject(xs) {
      let _788___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv0 = xs;
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_788___accumulator, _dafny.Seq.of());
        } else {
          let _789_wpOp = ((xs)[_dafny.ZERO]).WeakestPreOperands(_dafny.ZERO);
          let _790_wpCap = ((xs)[_dafny.ZERO]).WeakestPreCapacity(_dafny.ZERO);
          let _791_obj = (((((xs)[_dafny.ZERO]).is_JUMPSeg) || (((xs)[_dafny.ZERO]).is_JUMPISeg)) ? (function (_pat_let0_0) {
            return function (_792_tgt) {
              return ProofObject.ProofObj.create_JUMP((_pat_let_tv0)[_dafny.ZERO], _789_wpOp, _790_wpCap, _792_tgt, _dafny.Map.Empty.slice());
            }(_pat_let0_0);
          }(SegBuilder.__default.JUMPResolver((xs)[_dafny.ZERO]))) : (((((xs)[_dafny.ZERO]).is_CONTSeg) ? (ProofObject.ProofObj.create_CONT((xs)[_dafny.ZERO], _789_wpOp, _790_wpCap, _dafny.Map.Empty.slice())) : (ProofObject.ProofObj.create_TERMINAL((xs)[_dafny.ZERO], _789_wpOp, _790_wpCap, _dafny.Map.Empty.slice())))));
          _788___accumulator = _dafny.Seq.Concat(_788___accumulator, _dafny.Seq.of(_791_obj));
          let _in81 = (xs).slice(_dafny.ONE);
          xs = _in81;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module ProofObjectBuilder
let ArgParser = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "ArgParser._default";
    }
    _parentTraits() {
      return [];
    }
    static _default_Main() {
      process.stdout.write((_dafny.Seq.UnicodeFromString("hello! Testing ArgParser!\n")).toVerbatimString(false));
      let _793_cli;
      let _nw0 = new ArgParser.ArgumentParser();
      _nw0.__ctor(_dafny.Seq.UnicodeFromString("<filename>"));
      _793_cli = _nw0;
      (_793_cli).AddOption(_dafny.Seq.UnicodeFromString("-o"), _dafny.Seq.UnicodeFromString("--one"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("No help provided"));
      (_793_cli).AddOption(_dafny.Seq.UnicodeFromString("-tw"), _dafny.Seq.UnicodeFromString("--two"), new BigNumber(2), _dafny.Seq.UnicodeFromString("don't do that!"));
      let _794_r;
      _794_r = _dafny.Seq.of(_dafny.Seq.UnicodeFromString("-one"), _dafny.Seq.UnicodeFromString("--two"), _dafny.Seq.UnicodeFromString("a1"), _dafny.Seq.UnicodeFromString("a2"), _dafny.Seq.UnicodeFromString("-unknwon"));
      let _source56 = (_793_cli).GetArgs(_dafny.Seq.UnicodeFromString("-o"), _794_r);
      if (_source56.is_Success) {
        let _795___mcc_h0 = (_source56).v;
        let _796_a = _795___mcc_h0;
        process.stdout.write((_dafny.Seq.UnicodeFromString("Success -o! has arguments:")).toVerbatimString(false));
        process.stdout.write(_dafny.toString(_796_a));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      } else {
        let _797___mcc_h1 = (_source56).msg;
        let _798_m = _797___mcc_h1;
        process.stdout.write((_dafny.Seq.UnicodeFromString("No -o! ")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      let _source57 = (_793_cli).GetArgs(_dafny.Seq.UnicodeFromString("--two"), _794_r);
      if (_source57.is_Success) {
        let _799___mcc_h2 = (_source57).v;
        let _800_a = _799___mcc_h2;
        process.stdout.write((_dafny.Seq.UnicodeFromString("Success -two! has arguments: ")).toVerbatimString(false));
        process.stdout.write(_dafny.toString(_800_a));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      } else {
        let _801___mcc_h3 = (_source57).msg;
        let _802_m = _801___mcc_h3;
        process.stdout.write((_dafny.Seq.UnicodeFromString("No --two! ")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      (_793_cli).PrintHelp();
      return;
    }
  };

  $module.CLIOption = class CLIOption {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_CLIOption(name, numArgs, desc) {
      let $dt = new CLIOption(0);
      $dt.name = name;
      $dt.numArgs = numArgs;
      $dt.desc = desc;
      return $dt;
    }
    get is_CLIOption() { return this.$tag === 0; }
    get dtor_name() { return this.name; }
    get dtor_numArgs() { return this.numArgs; }
    get dtor_desc() { return this.desc; }
    toString() {
      if (this.$tag === 0) {
        return "ArgParser.CLIOption.CLIOption" + "(" + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.numArgs) + ", " + this.desc.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.name, other.name) && _dafny.areEqual(this.numArgs, other.numArgs) && _dafny.areEqual(this.desc, other.desc);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ArgParser.CLIOption.create_CLIOption('', _dafny.ZERO, '');
    }
    static Rtd() {
      return class {
        static get Default() {
          return CLIOption.Default();
        }
      };
    }
  }

  $module.ArgumentParser = class ArgumentParser {
    constructor () {
      this._tname = "ArgParser.ArgumentParser";
      this.knownArgs = _dafny.Map.Empty;
      this.knownNameArgs = _dafny.Map.Empty;
      this.knownKeys = _dafny.Seq.of();
      this.usageSuffix = '';
    }
    _parentTraits() {
      return [];
    }
    __ctor(s) {
      let _this = this;
      (_this).usageSuffix = s;
      (_this).knownArgs = _dafny.Map.Empty.slice().updateUnsafe(_dafny.Seq.UnicodeFromString("--help"),ArgParser.CLIOption.create_CLIOption(_dafny.Seq.UnicodeFromString("-h"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Display help and exit")));
      (_this).knownNameArgs = _dafny.Map.Empty.slice().updateUnsafe(_dafny.Seq.UnicodeFromString("-h"),_dafny.Seq.UnicodeFromString("--help"));
      (_this).knownKeys = _dafny.Seq.of(_dafny.Seq.UnicodeFromString("--help"));
      return;
    }
    AddOption(opname, name, numArgs, help) {
      let _this = this;
      (_this).knownArgs = (_this.knownArgs).update(name, ArgParser.CLIOption.create_CLIOption(opname, numArgs, help));
      (_this).knownNameArgs = (_this.knownNameArgs).update(opname, name);
      if (!_dafny.Seq.contains(_this.knownKeys, name)) {
        (_this).knownKeys = _dafny.Seq.Concat(_this.knownKeys, _dafny.Seq.of(name));
      }
      return;
    }
    PrintHelp() {
      let _this = this;
      process.stdout.write((_dafny.Seq.UnicodeFromString("usage: <this program> ")).toVerbatimString(false));
      let _hi0 = new BigNumber((_this.knownKeys).length);
      for (let _803_i = _dafny.ZERO; _803_i.isLessThan(_hi0); _803_i = _803_i.plus(_dafny.ONE)) {
        let _804_k;
        _804_k = (_this.knownArgs).get((_this.knownKeys)[_803_i]);
        process.stdout.write((_dafny.Seq.UnicodeFromString(" [")).toVerbatimString(false));
        process.stdout.write(((_this.knownKeys)[_803_i]).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("] ")).toVerbatimString(false));
        let _hi1 = (_804_k).dtor_numArgs;
        for (let _805_i = _dafny.ZERO; _805_i.isLessThan(_hi1); _805_i = _805_i.plus(_dafny.ONE)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString(" arg")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(_805_i));
        }
      }
      process.stdout.write((_dafny.Seq.UnicodeFromString(" ")).toVerbatimString(false));
      process.stdout.write((_this.usageSuffix).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("options")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      let _806_maxL;
      _806_maxL = (_this).MaxValueFast(_this.knownKeys, _dafny.ZERO);
      let _hi2 = new BigNumber((_this.knownKeys).length);
      for (let _807_i = _dafny.ZERO; _807_i.isLessThan(_hi2); _807_i = _807_i.plus(_dafny.ONE)) {
        let _808_k;
        _808_k = (_this.knownArgs).get((_this.knownKeys)[_807_i]);
        process.stdout.write(((_this.knownKeys)[_807_i]).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.Create(((_806_maxL).minus(new BigNumber(((_this.knownKeys)[_807_i]).length))).plus(new BigNumber(2)), function (_809___v0) {
          return new _dafny.CodePoint(' '.codePointAt(0));
        })).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString(" [")).toVerbatimString(false));
        process.stdout.write(((_808_k).dtor_name).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("] ")).toVerbatimString(false));
        process.stdout.write(((_808_k).dtor_desc).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      return;
    }
    GetArgs(key, s) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Try.create_Failure(_dafny.Seq.UnicodeFromString("Not found"));
        } else if (!((_this.knownArgs).Keys).contains(key)) {
          return MiscTypes.Try.create_Failure(_dafny.Seq.UnicodeFromString("Not a key"));
        } else if (_dafny.areEqual((_this).Canonical((s)[_dafny.ZERO]), key)) {
          let _810_opt = (_this.knownArgs).get(key);
          let _811_numArgs = (_810_opt).dtor_numArgs;
          if ((new BigNumber(((s).slice(_dafny.ONE)).length)).isLessThan(_811_numArgs)) {
            return MiscTypes.Try.create_Failure(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("argument "), (s)[_dafny.ZERO]), _dafny.Seq.UnicodeFromString(" needs more arguments")));
          } else {
            return MiscTypes.Try.create_Success(((s).slice(_dafny.ONE)).slice(0, _811_numArgs));
          }
        } else {
          let _in82 = _this;
          let _in83 = key;
          let _in84 = (s).slice(_dafny.ONE);
          _this = _in82;
          ;
          key = _in83;
          s = _in84;
          continue TAIL_CALL_START;
        }
      }
    };
    Canonical(s) {
      let _this = this;
      if ((_this.knownNameArgs).contains(s)) {
        return (_this.knownNameArgs).get(s);
      } else {
        return s;
      }
    };
    MaxValueFast(s, max) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return max;
        } else {
          let _in85 = _this;
          let _in86 = (s).slice(_dafny.ONE);
          let _in87 = Int.__default.Max(new BigNumber(((s)[_dafny.ZERO]).length), max);
          _this = _in85;
          ;
          s = _in86;
          max = _in87;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module ArgParser
let SeqOfSets = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "SeqOfSets._default";
    }
    _parentTraits() {
      return [];
    }
    static SetU(xs) {
      let _812___accumulator = _dafny.Set.fromElements();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.Set.fromElements()).Union(_812___accumulator);
        } else {
          _812___accumulator = (_812___accumulator).Union((xs)[_dafny.ZERO]);
          let _in88 = (xs).slice(_dafny.ONE);
          xs = _in88;
          continue TAIL_CALL_START;
        }
      }
    };
    static SetI(xs) {
      if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Set.fromElements();
      } else if ((new BigNumber((xs).length)).isEqualTo(_dafny.ONE)) {
        return (xs)[_dafny.ZERO];
      } else {
        return ((xs)[_dafny.ZERO]).Intersect(SeqOfSets.__default.SetI((xs).slice(_dafny.ONE)));
      }
    };
    static AllNonEmpty(xs) {
      return _dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber((xs).length)), true, function (_forall_var_4) {
        let _813_k = _forall_var_4;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_813_k)) && ((_813_k).isLessThan(new BigNumber((xs).length)))) || (!((xs)[_813_k]).equals(_dafny.Set.fromElements()));
      });
    };
    static DisjointAnyTwo(xs) {
      return _dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber((xs).length)), true, function (_forall_var_5) {
        let _814_k = _forall_var_5;
        return _dafny.Quantifier(_dafny.IntegerRange((_814_k).plus(_dafny.ONE), new BigNumber((xs).length)), true, function (_forall_var_6) {
          let _815_k_k = _forall_var_6;
          return !((((_dafny.ZERO).isLessThanOrEqualTo(_814_k)) && ((_814_k).isLessThan(_815_k_k))) && ((_815_k_k).isLessThan(new BigNumber((xs).length)))) || ((((xs)[_814_k]).Intersect((xs)[_815_k_k])).equals(_dafny.Set.fromElements()));
        });
      });
    };
    static SetN(xs, n) {
      return (SeqOfSets.__default.SetU(xs)).equals(function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of _dafny.IntegerRange(_dafny.ZERO, n)) {
          let _816_z = _compr_0;
          if (((_dafny.ZERO).isLessThanOrEqualTo(_816_z)) && ((_816_z).isLessThan(n))) {
            _coll0.add(_816_z);
          }
        }
        return _coll0;
      }());
    };
    static SplitSet(xs, f) {
      let _817_asSeq = SeqOfSets.__default.SetToSequence(xs);
      return SeqOfSets.__default.SplitSeqTail(_817_asSeq, f, _dafny.Set.fromElements(), _dafny.Set.fromElements(), _dafny.ZERO);
    };
    static SplitSeqOfSet(xs, f) {
      let _818___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_818___accumulator, _dafny.Seq.of());
        } else {
          _818___accumulator = _dafny.Seq.Concat(_818___accumulator, _dafny.Seq.of(SeqOfSets.__default.SplitSet((xs)[_dafny.ZERO], f)));
          let _in89 = (xs).slice(_dafny.ONE);
          let _in90 = f;
          xs = _in89;
          f = _in90;
          continue TAIL_CALL_START;
        }
      }
    };
    static SetToSequence(s) {
      let _819___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv1 = s;
        if ((s).equals(_dafny.Set.fromElements())) {
          return _dafny.Seq.Concat(_819___accumulator, _dafny.Seq.of());
        } else {
          return function (_let_dummy_1) {
            let _820_x = undefined;
            L_ASSIGN_SUCH_THAT_0: {
              for (const _assign_such_that_0 of (s).Elements) {
                _820_x = _assign_such_that_0;
                if (((s).contains(_820_x)) && (_dafny.Quantifier((s).Elements, true, function (_forall_var_7) {
                  let _821_y = _forall_var_7;
                  return !((s).contains(_821_y)) || ((_820_x).isLessThanOrEqualTo(_821_y));
                }))) {
                  break L_ASSIGN_SUCH_THAT_0;
                }
              }
              throw new Error("assign-such-that search produced no value (line 193)");
            }
            return _dafny.Seq.Concat(_dafny.Seq.of(_820_x), SeqOfSets.__default.SetToSequence((_pat_let_tv1).Difference(_dafny.Set.fromElements(_820_x))));
          }(0);
        }
      }
    };
    static SplitSeqTail(xs, f, cTrue, cFalse, index) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(index)) {
          return _dafny.Tuple.of(cTrue, cFalse);
        } else if ((f)((xs)[index])) {
          let _in91 = xs;
          let _in92 = f;
          let _in93 = (cTrue).Union(_dafny.Set.fromElements((xs)[index]));
          let _in94 = cFalse;
          let _in95 = (index).plus(_dafny.ONE);
          xs = _in91;
          f = _in92;
          cTrue = _in93;
          cFalse = _in94;
          index = _in95;
          continue TAIL_CALL_START;
        } else {
          let _in96 = xs;
          let _in97 = f;
          let _in98 = cTrue;
          let _in99 = (cFalse).Union(_dafny.Set.fromElements((xs)[index]));
          let _in100 = (index).plus(_dafny.ONE);
          xs = _in96;
          f = _in97;
          cTrue = _in98;
          cFalse = _in99;
          index = _in100;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module SeqOfSets
let PartitionMod = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "PartitionMod._default";
    }
    _parentTraits() {
      return [];
    }
    static SplitAll(p, f, index, max) {
      TAIL_CALL_START: while (true) {
        if ((max).isEqualTo(index)) {
          return p;
        } else {
          let _822_f_k = ((_823_f, _824_max, _825_index) => function (_826_x) {
            return (_823_f)((_826_x).plus(_dafny.ONE));
          })(f, max, index);
          let _827_p1 = (p).SplitAt((f)(_dafny.ZERO), _dafny.ZERO);
          let _in101 = _827_p1;
          let _in102 = _822_f_k;
          let _in103 = (index).plus(_dafny.ONE);
          let _in104 = max;
          p = _in101;
          f = _in102;
          index = _in103;
          max = _in104;
          continue TAIL_CALL_START;
        }
      }
    };
    static PrintPartition(p) {
      let _hi3 = new BigNumber(((p).dtor_elem).length);
      for (let _828_k = _dafny.ZERO; _828_k.isLessThan(_hi3); _828_k = _828_k.plus(_dafny.ONE)) {
        let _829_setToSeq;
        _829_setToSeq = SeqOfSets.__default.SetToSequence(((p).dtor_elem)[_828_k]);
        process.stdout.write(_dafny.toString(_829_setToSeq));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      return;
    }
  };

  $module.ValidPartition = class ValidPartition {
    constructor () {
    }
    static get Witness() {
      return PartitionMod.Partition.create_Partition(_dafny.ONE, _dafny.Seq.of(_dafny.Set.fromElements(_dafny.ZERO)));
    }
    static get Default() {
      return PartitionMod.ValidPartition.Witness;
    }
  };

  $module.Partition = class Partition {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Partition(n, elem) {
      let $dt = new Partition(0);
      $dt.n = n;
      $dt.elem = elem;
      return $dt;
    }
    get is_Partition() { return this.$tag === 0; }
    get dtor_n() { return this.n; }
    get dtor_elem() { return this.elem; }
    toString() {
      if (this.$tag === 0) {
        return "PartitionMod.Partition.Partition" + "(" + _dafny.toString(this.n) + ", " + _dafny.toString(this.elem) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.n, other.n) && _dafny.areEqual(this.elem, other.elem);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return PartitionMod.Partition.create_Partition(_dafny.ZERO, _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return Partition.Default();
        }
      };
    }
    SplitAt(f, index) {
      let _this = this;
      let _830_r = SeqOfSets.__default.SplitSet(((_this).dtor_elem)[index], f);
      if ((!((_830_r)[0]).equals(_dafny.Set.fromElements())) && (!((_830_r)[1]).equals(_dafny.Set.fromElements()))) {
        let _831_j = _dafny.Seq.Concat(_dafny.Seq.Concat(((_this).dtor_elem).slice(0, index), ((_this).dtor_elem).slice((index).plus(_dafny.ONE))), _dafny.Seq.of((_830_r)[0], (_830_r)[1]));
        let _832_pp = PartitionMod.Partition.create_Partition((_this).dtor_n, _831_j);
        return _832_pp;
      } else if (!((_830_r)[0]).equals(_dafny.Set.fromElements())) {
        let _833_j = _dafny.Seq.Concat(_dafny.Seq.Concat(((_this).dtor_elem).slice(0, index), ((_this).dtor_elem).slice((index).plus(_dafny.ONE))), _dafny.Seq.of((_830_r)[0]));
        return PartitionMod.Partition.create_Partition((_this).dtor_n, _833_j);
      } else {
        let _834_j = _dafny.Seq.Concat(_dafny.Seq.Concat(((_this).dtor_elem).slice(0, index), ((_this).dtor_elem).slice((index).plus(_dafny.ONE))), _dafny.Seq.of((_830_r)[1]));
        return PartitionMod.Partition.create_Partition((_this).dtor_n, _834_j);
      }
    };
    GetClass(x, index) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((((_this).dtor_elem)[index]).contains(x)) {
          return index;
        } else {
          let _in105 = _this;
          let _in106 = x;
          let _in107 = (index).plus(_dafny.ONE);
          _this = _in105;
          ;
          x = _in106;
          index = _in107;
          continue TAIL_CALL_START;
        }
      }
    };
    Equiv(x, y) {
      let _this = this;
      return ((_this).GetClass(x, _dafny.ZERO)).isEqualTo((_this).GetClass(y, _dafny.ZERO));
    };
    Refines2(p) {
      let _this = this;
      return _dafny.Quantifier(((_this).dtor_elem).UniqueElements, true, function (_forall_var_8) {
        let _835_k = _forall_var_8;
        return !(_dafny.Seq.contains((_this).dtor_elem, _835_k)) || (_dafny.Quantifier(((p).dtor_elem).UniqueElements, false, function (_exists_var_0) {
          let _836_c = _exists_var_0;
          return (_dafny.Seq.contains((p).dtor_elem, _836_c)) && ((_835_k).IsSubsetOf(_836_c));
        }));
      });
    };
    Refines(p) {
      let _this = this;
      return (true) && ((new BigNumber(((p).dtor_elem).length)).isLessThanOrEqualTo(new BigNumber(((_this).dtor_elem).length)));
    };
  }
  return $module;
})(); // end of module PartitionMod
let Automata = (function() {
  let $module = {};


  $module.ValidAuto = class ValidAuto {
    constructor () {
    }
    static get Witness() {
      return Automata.Auto.create_Auto(_dafny.ZERO, _dafny.Map.Empty.slice());
    }
    static get Default() {
      return Automata.ValidAuto.Witness;
    }
  };

  $module.Auto = class Auto {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Auto(numStates, transitions) {
      let $dt = new Auto(0);
      $dt.numStates = numStates;
      $dt.transitions = transitions;
      return $dt;
    }
    get is_Auto() { return this.$tag === 0; }
    get dtor_numStates() { return this.numStates; }
    get dtor_transitions() { return this.transitions; }
    toString() {
      if (this.$tag === 0) {
        return "Automata.Auto.Auto" + "(" + _dafny.toString(this.numStates) + ", " + _dafny.toString(this.transitions) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.numStates, other.numStates) && _dafny.areEqual(this.transitions, other.transitions);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Automata.Auto.create_Auto(_dafny.ZERO, _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Auto.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      return _dafny.Quantifier(((_this).dtor_transitions).Keys.Elements, true, function (_forall_var_9) {
        let _837_k = _forall_var_9;
        return !(((_this).dtor_transitions).contains(_837_k)) || ((((_this).dtor_transitions).get(_837_k)).isLessThan((_this).dtor_numStates));
      });
    };
    Succ(s, l) {
      let _this = this;
      if (((_this).dtor_transitions).contains(_dafny.Tuple.of(s, l))) {
        return MiscTypes.Option.create_Some(((_this).dtor_transitions).get(_dafny.Tuple.of(s, l)));
      } else {
        return MiscTypes.Option.create_None();
      }
    };
  }
  return $module;
})(); // end of module Automata
let Minimiser = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Minimiser._default";
    }
    _parentTraits() {
      return [];
    }
    static Minimise(ap) {
      let _838_p1 = (ap).SplitFrom();
      if ((new BigNumber((((_838_p1).dtor_p).dtor_elem).length)).isEqualTo(new BigNumber((((ap).dtor_p).dtor_elem).length))) {
        return _838_p1;
      } else {
        return Minimiser.__default.Minimise(_838_p1);
      }
    };
  };

  $module.ValidPair = class ValidPair {
    constructor () {
    }
    static get Witness() {
      return Minimiser.Pair.create_Pair(Automata.Auto.create_Auto(_dafny.ONE, _dafny.Map.Empty.slice()), PartitionMod.Partition.create_Partition(_dafny.ONE, _dafny.Seq.of(_dafny.Set.fromElements(_dafny.ZERO))));
    }
    static get Default() {
      return Minimiser.ValidPair.Witness;
    }
  };

  $module.Pair = class Pair {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pair(a, p) {
      let $dt = new Pair(0);
      $dt.a = a;
      $dt.p = p;
      return $dt;
    }
    get is_Pair() { return this.$tag === 0; }
    get dtor_a() { return this.a; }
    get dtor_p() { return this.p; }
    toString() {
      if (this.$tag === 0) {
        return "Minimiser.Pair.Pair" + "(" + _dafny.toString(this.a) + ", " + _dafny.toString(this.p) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.a, other.a) && _dafny.areEqual(this.p, other.p);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Minimiser.Pair.create_Pair(Automata.ValidAuto.Default, PartitionMod.ValidPartition.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Pair.Default();
        }
      };
    }
    IsValid() {
      let _this = this;
      return (((_this).dtor_a).dtor_numStates).isEqualTo(((_this).dtor_p).dtor_n);
    };
    Auto() {
      let _this = this;
      return (_this).dtor_a;
    };
    Parts() {
      let _this = this;
      return (_this).dtor_p;
    };
    ClassSucc(x) {
      let _this = this;
      let _839_s1 = function (_source58) {
        if (_source58.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _840___mcc_h0 = (_source58).v;
          return function (_pat_let2_0) {
            return function (_841_n) {
              return MiscTypes.Option.create_Some(((_this).dtor_p).GetClass(_841_n, _dafny.ZERO));
            }(_pat_let2_0);
          }(_840___mcc_h0);
        }
      }(((_this).dtor_a).Succ(x, false));
      let _842_s2 = function (_source59) {
        if (_source59.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _843___mcc_h1 = (_source59).v;
          return function (_pat_let3_0) {
            return function (_844_n) {
              return MiscTypes.Option.create_Some(((_this).dtor_p).GetClass(_844_n, _dafny.ZERO));
            }(_pat_let3_0);
          }(_843___mcc_h1);
        }
      }(((_this).dtor_a).Succ(x, true));
      return _dafny.Tuple.of(_839_s1, _842_s2);
    };
    SplitFrom() {
      let _this = this;
      let _845_splitterF = function (_846_k) {
        return ((_847_k) => function (_848_y) {
          return _dafny.areEqual((_this).ClassSucc((SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[_847_k]))[_dafny.ZERO]), (_this).ClassSucc(_848_y));
        })(_846_k);
      };
      let _849_r = PartitionMod.__default.SplitAll((_this).dtor_p, _845_splitterF, _dafny.ZERO, new BigNumber((((_this).dtor_p).dtor_elem).length));
      let _850_dt__update__tmp_h0 = _this;
      let _851_dt__update_hp_h0 = _849_r;
      return Minimiser.Pair.create_Pair((_850_dt__update__tmp_h0).dtor_a, _851_dt__update_hp_h0);
    };
    GenerateReducedTailRec(index, acc) {
      let _this = this;
      if ((index).isEqualTo(new BigNumber((((_this).dtor_p).dtor_elem).length))) {
        return acc;
      } else {
        let _852_firstElem = (SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[index]))[_dafny.ZERO];
        let _853_succs = (_this).ClassSucc(_852_firstElem);
        let _854_newEdges = function (_source60) {
          let _855___mcc_h0 = (_source60)[0];
          let _856___mcc_h1 = (_source60)[1];
          return function (_source61) {
            if (_source61.is_None) {
              return function (_source62) {
                if (_source62.is_None) {
                  return _dafny.Seq.of();
                } else {
                  let _857___mcc_h2 = (_source62).v;
                  return function (_pat_let4_0) {
                    return function (_858_sTrue) {
                      return _dafny.Seq.of(_dafny.Tuple.of(_852_firstElem, true, (SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[_858_sTrue]))[_dafny.ZERO]));
                    }(_pat_let4_0);
                  }(_857___mcc_h2);
                }
              }(_856___mcc_h1);
            } else {
              let _859___mcc_h3 = (_source61).v;
              return function (_source63) {
                if (_source63.is_None) {
                  return function (_pat_let5_0) {
                    return function (_860_sFalse) {
                      return _dafny.Seq.of(_dafny.Tuple.of(_852_firstElem, false, (SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[_860_sFalse]))[_dafny.ZERO]));
                    }(_pat_let5_0);
                  }(_859___mcc_h3);
                } else {
                  let _861___mcc_h4 = (_source63).v;
                  return function (_pat_let6_0) {
                    return function (_862_sTrue) {
                      return function (_pat_let7_0) {
                        return function (_863_sFalse) {
                          return _dafny.Seq.of(_dafny.Tuple.of(_852_firstElem, false, (SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[_863_sFalse]))[_dafny.ZERO]), _dafny.Tuple.of(_852_firstElem, true, (SeqOfSets.__default.SetToSequence((((_this).dtor_p).dtor_elem)[_862_sTrue]))[_dafny.ZERO]));
                        }(_pat_let7_0);
                      }(_859___mcc_h3);
                    }(_pat_let6_0);
                  }(_861___mcc_h4);
                }
              }(_856___mcc_h1);
            }
          }(_855___mcc_h0);
        }(_dafny.Tuple.of((_853_succs)[0], (_853_succs)[1]));
        return (_this).GenerateReducedTailRec((index).plus(_dafny.ONE), _dafny.Seq.Concat(acc, _854_newEdges));
      }
    };
  }
  return $module;
})(); // end of module Minimiser
let CFGraph = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "CFGraph._default";
    }
    _parentTraits() {
      return [];
    }
    static BoolSeqToNat(xb) {
      if ((new BigNumber((xb).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.ZERO;
      } else {
        return ((((xb)[_dafny.ZERO]) ? (_dafny.ONE) : (_dafny.ZERO))).plus((new BigNumber(2)).multipliedBy(CFGraph.__default.BoolSeqToNat((xb).slice(_dafny.ONE))));
      }
    };
    static SegNumPartition(p, m, maxSegNum, n) {
      TAIL_CALL_START: while (true) {
        if ((n).isLessThanOrEqualTo(maxSegNum)) {
          let _864_f = ((_865_m, _866_n, _867_p) => function (_868_x) {
            return _dafny.areEqual(((_865_m).get(_868_x)).dtor_seg, MiscTypes.Option.create_Some(_866_n));
          })(m, n, p);
          let _869_p1 = (p).SplitAt(_864_f, (new BigNumber(((p).dtor_elem).length)).minus(_dafny.ONE));
          let _in108 = _869_p1;
          let _in109 = m;
          let _in110 = maxSegNum;
          let _in111 = (n).plus(_dafny.ONE);
          p = _in108;
          m = _in109;
          maxSegNum = _in110;
          n = _in111;
          continue TAIL_CALL_START;
        } else {
          return p;
        }
      }
    };
    static EdgesToMap(edges, seenNodes, reverseSeenNodes, builtMap, lastNum, index) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((edges).length)).isEqualTo(index)) {
          return _dafny.Tuple.of(lastNum, builtMap, seenNodes, reverseSeenNodes);
        } else {
          let _let_tmp_rhs0 = ((((seenNodes).Keys).contains(((edges)[index]).dtor_src)) ? (_dafny.Tuple.of((seenNodes).get(((edges)[index]).dtor_src), lastNum, seenNodes, reverseSeenNodes)) : (_dafny.Tuple.of((lastNum).plus(_dafny.ONE), (lastNum).plus(_dafny.ONE), (seenNodes).update(((edges)[index]).dtor_src, (lastNum).plus(_dafny.ONE)), (reverseSeenNodes).update((lastNum).plus(_dafny.ONE), ((edges)[index]).dtor_src))));
          let _870_src = (_let_tmp_rhs0)[0];
          let _871_last = (_let_tmp_rhs0)[1];
          let _872_m1 = (_let_tmp_rhs0)[2];
          let _873_rm1 = (_let_tmp_rhs0)[3];
          let _let_tmp_rhs1 = ((((_872_m1).Keys).contains(((edges)[index]).dtor_tgt)) ? (_dafny.Tuple.of((_872_m1).get(((edges)[index]).dtor_tgt), _871_last, _872_m1, _873_rm1)) : (_dafny.Tuple.of((_871_last).plus(_dafny.ONE), (_871_last).plus(_dafny.ONE), (_872_m1).update(((edges)[index]).dtor_tgt, (_871_last).plus(_dafny.ONE)), (_873_rm1).update((_871_last).plus(_dafny.ONE), ((edges)[index]).dtor_tgt))));
          let _874_tgt = (_let_tmp_rhs1)[0];
          let _875_last_k = (_let_tmp_rhs1)[1];
          let _876_m2 = (_let_tmp_rhs1)[2];
          let _877_rm2 = (_let_tmp_rhs1)[3];
          let _878_b = (builtMap).update(_dafny.Tuple.of(_870_src, ((edges)[index]).dtor_lab), _874_tgt);
          let _in112 = edges;
          let _in113 = _876_m2;
          let _in114 = _877_rm2;
          let _in115 = _878_b;
          let _in116 = _875_last_k;
          let _in117 = (index).plus(_dafny.ONE);
          edges = _in112;
          seenNodes = _in113;
          reverseSeenNodes = _in114;
          builtMap = _in115;
          lastNum = _in116;
          index = _in117;
          continue TAIL_CALL_START;
        }
      }
    };
    static BoolsToString(x) {
      let _879___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((x).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_879___accumulator, _dafny.Seq.UnicodeFromString("E"));
        } else {
          _879___accumulator = _dafny.Seq.Concat(_879___accumulator, _dafny.Seq.of((((x)[_dafny.ZERO]) ? (new _dafny.CodePoint('1'.codePointAt(0))) : (new _dafny.CodePoint('0'.codePointAt(0))))));
          let _in118 = (x).slice(_dafny.ONE);
          x = _in118;
          continue TAIL_CALL_START;
        }
      }
    };
    static SegColour(s) {
      let _source64 = s;
      if (_source64.is_JUMPSeg) {
        let _880___mcc_h0 = (_source64).ins;
        let _881___mcc_h1 = (_source64).lastIns;
        let _882___mcc_h2 = (_source64).netOpEffect;
        return _dafny.Seq.UnicodeFromString("");
      } else if (_source64.is_JUMPISeg) {
        let _883___mcc_h6 = (_source64).ins;
        let _884___mcc_h7 = (_source64).lastIns;
        let _885___mcc_h8 = (_source64).netOpEffect;
        return CFGraph.__default.branchColour;
      } else if (_source64.is_RETURNSeg) {
        let _886___mcc_h12 = (_source64).ins;
        let _887___mcc_h13 = (_source64).lastIns;
        let _888___mcc_h14 = (_source64).netOpEffect;
        return CFGraph.__default.returnColour;
      } else if (_source64.is_STOPSeg) {
        let _889___mcc_h18 = (_source64).ins;
        let _890___mcc_h19 = (_source64).lastIns;
        let _891___mcc_h20 = (_source64).netOpEffect;
        return CFGraph.__default.revertColour;
      } else if (_source64.is_CONTSeg) {
        let _892___mcc_h24 = (_source64).ins;
        let _893___mcc_h25 = (_source64).lastIns;
        let _894___mcc_h26 = (_source64).netOpEffect;
        return _dafny.Seq.UnicodeFromString("");
      } else {
        let _895___mcc_h30 = (_source64).ins;
        let _896___mcc_h31 = (_source64).lastIns;
        let _897___mcc_h32 = (_source64).netOpEffect;
        return CFGraph.__default.invalidColour;
      }
    };
    static DOTSeg(s, numSeg) {
      let _898_jumpTip = ((((s).is_JUMPSeg) || ((s).is_JUMPISeg)) ? (function (_pat_let8_0) {
        return function (_899_r) {
          return function (_source65) {
            if (_source65.is_Left) {
              let _900___mcc_h0 = (_source65).l;
              return function (_pat_let9_0) {
                return function (_901_v) {
                  return function (_source66) {
                    if (_source66.is_Value) {
                      let _902___mcc_h2 = (_source66).v;
                      return function (_pat_let10_0) {
                        return function (_903_address) {
                          return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Constant 0x"), Hex.__default.NatToHex(_903_address));
                        }(_pat_let10_0);
                      }(_902___mcc_h2);
                    } else {
                      let _904___mcc_h3 = (_source66).s;
                      return function (_pat_let11_0) {
                        return function (_905_msg) {
                          return _dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Unknown");
                        }(_pat_let11_0);
                      }(_904___mcc_h3);
                    }
                  }(_901_v);
                }(_pat_let9_0);
              }(_900___mcc_h0);
            } else {
              let _906___mcc_h1 = (_source65).r;
              return function (_pat_let12_0) {
                return function (_907_stackPos) {
                  return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Stack on Entry.Peek("), Int.__default.NatToString(_907_stackPos)), _dafny.Seq.UnicodeFromString(")"));
                }(_pat_let12_0);
              }(_906___mcc_h1);
            }
          }(_899_r);
        }(_pat_let8_0);
      }(SegBuilder.__default.JUMPResolver(s))) : (_dafny.Seq.UnicodeFromString("")));
      let _908_stackSizeEffect = _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Stack Size &#916;: "), Int.__default.IntToString((s).StackEffect()));
      let _909_mninNumOpe = _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("&#10;Stack Size on Entry &#8805; "), Int.__default.NatToString((s).WeakestPreOperands(_dafny.ZERO)));
      let _910_prefix = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<B>Segment "), Int.__default.NatToString(numSeg)), _dafny.Seq.UnicodeFromString(" [0x")), Hex.__default.NatToHex((s).StartAddress())), _dafny.Seq.UnicodeFromString("]</B><BR ALIGN=\"CENTER\"/>\n"));
      let _911_body = CFGraph.__default.DOTIns((s).Ins());
      return _dafny.Tuple.of(_dafny.Seq.Concat(_910_prefix, _911_body), _dafny.Seq.Concat(_dafny.Seq.Concat(_908_stackSizeEffect, _898_jumpTip), _909_mninNumOpe));
    };
    static DOTSegTable(s, numSeg) {
      let _912_jumpTip = ((((s).is_JUMPSeg) || ((s).is_JUMPISeg)) ? (function (_pat_let13_0) {
        return function (_913_r) {
          return function (_source67) {
            if (_source67.is_Left) {
              let _914___mcc_h0 = (_source67).l;
              return function (_pat_let14_0) {
                return function (_915_v) {
                  return function (_source68) {
                    if (_source68.is_Value) {
                      let _916___mcc_h2 = (_source68).v;
                      return function (_pat_let15_0) {
                        return function (_917_address) {
                          return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Constant 0x"), Hex.__default.NatToHex(_917_address));
                        }(_pat_let15_0);
                      }(_916___mcc_h2);
                    } else {
                      let _918___mcc_h3 = (_source68).s;
                      return function (_pat_let16_0) {
                        return function (_919_msg) {
                          return _dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Unknown");
                        }(_pat_let16_0);
                      }(_918___mcc_h3);
                    }
                  }(_915_v);
                }(_pat_let14_0);
              }(_914___mcc_h0);
            } else {
              let _920___mcc_h1 = (_source67).r;
              return function (_pat_let17_0) {
                return function (_921_stackPos) {
                  return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("&#10;Exit Jump target: Stack on Entry.Peek("), Int.__default.NatToString(_921_stackPos)), _dafny.Seq.UnicodeFromString(")"));
                }(_pat_let17_0);
              }(_920___mcc_h1);
            }
          }(_913_r);
        }(_pat_let13_0);
      }(SegBuilder.__default.JUMPResolver(s))) : (_dafny.Seq.UnicodeFromString("")));
      let _922_tableStart = _dafny.Seq.UnicodeFromString("<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n");
      let _923_prefix = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TR><TD "), _dafny.Seq.UnicodeFromString(">Segment ")), Int.__default.NatToString(numSeg)), _dafny.Seq.UnicodeFromString(" [0x")), Hex.__default.NatToHex((s).StartAddress())), _dafny.Seq.UnicodeFromString("]</TD>")), _dafny.Seq.UnicodeFromString("<TD")), _dafny.Seq.UnicodeFromString(" href=\"\" tooltip=\"Stack Size &#916;: ")), Int.__default.IntToString((s).StackEffect())), _dafny.Seq.UnicodeFromString("&#10;Stack Size on Entry &#8805; ")), Int.__default.NatToString((s).WeakestPreOperands(_dafny.ZERO))), _912_jumpTip), _dafny.Seq.UnicodeFromString("\"")), _dafny.Seq.UnicodeFromString("><FONT color=\"green\">&#9636;</FONT></TD>")), _dafny.Seq.UnicodeFromString("</TR><HR/>\n"));
      let _924_tableEnd = _dafny.Seq.UnicodeFromString("</TABLE>\n");
      let _925_body = CFGraph.__default.DOTInsTable((s).Ins(), true);
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_922_tableStart, _923_prefix), _925_body), _924_tableEnd);
    };
    static DOTIns(xi) {
      let _926___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xi).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_926___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _926___accumulator = _dafny.Seq.Concat(_926___accumulator, ((xi)[_dafny.ZERO]).ToHTML());
          let _in119 = (xi).slice(_dafny.ONE);
          xi = _in119;
          continue TAIL_CALL_START;
        }
      }
    };
    static DOTInsTable(xi, isFirst) {
      let _927___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xi).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_927___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          let _928_prefix = _dafny.Seq.UnicodeFromString("<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n");
          let _929_suffix = _dafny.Seq.UnicodeFromString("</TD></TR>\n");
          let _930_exitPortTag = ((((xi)[_dafny.ZERO]).IsJump()) ? (_dafny.Seq.UnicodeFromString("PORT=\"exit\"")) : (_dafny.Seq.UnicodeFromString("")));
          let _931_entryPortTag = ((isFirst) ? (_dafny.Seq.UnicodeFromString("PORT=\"entry\"")) : (_dafny.Seq.UnicodeFromString("")));
          let _932_a = ((xi)[_dafny.ZERO]).ToHTMLTable(_931_entryPortTag, _930_exitPortTag);
          _927___accumulator = _dafny.Seq.Concat(_927___accumulator, _dafny.Seq.Concat(_dafny.Seq.Concat(_928_prefix, _932_a), _929_suffix));
          let _in120 = (xi).slice(_dafny.ONE);
          let _in121 = false;
          xi = _in120;
          isFirst = _in121;
          continue TAIL_CALL_START;
        }
      }
    };
    static NatBoolEdgesToCFGEdges(xs, m, maxSegNum) {
      let _933___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_933___accumulator, _dafny.Seq.of());
        } else {
          _933___accumulator = _dafny.Seq.Concat(_933___accumulator, _dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge((m).get(((xs)[_dafny.ZERO])[0]), ((xs)[_dafny.ZERO])[1], (m).get(((xs)[_dafny.ZERO])[2]))));
          let _in122 = (xs).slice(_dafny.ONE);
          let _in123 = m;
          let _in124 = maxSegNum;
          xs = _in122;
          m = _in123;
          maxSegNum = _in124;
          continue TAIL_CALL_START;
        }
      }
    };
    static get jcolour() {
      return _dafny.Seq.UnicodeFromString("royalblue");
    };
    static get jumpColour() {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("color="), CFGraph.__default.jcolour), _dafny.Seq.UnicodeFromString(","));
    };
    static get skcolour() {
      return _dafny.Seq.UnicodeFromString("black");
    };
    static get skipColour() {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("color="), CFGraph.__default.skcolour), _dafny.Seq.UnicodeFromString(","));
    };
    static get revertColour() {
      return _dafny.Seq.UnicodeFromString("style=filled,color=orange,fontcolor=white,");
    };
    static get returnColour() {
      return _dafny.Seq.UnicodeFromString("style=filled,color=olivedrab,fontcolor=white,");
    };
    static get invalidColour() {
      return _dafny.Seq.UnicodeFromString("style=filled,color=firebrick,fontcolor=white,");
    };
    static get branchColour() {
      return _dafny.Seq.UnicodeFromString("");
    };
  };

  $module.CFGNode = class CFGNode {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_CFGNode(id, seg) {
      let $dt = new CFGNode(0);
      $dt.id = id;
      $dt.seg = seg;
      return $dt;
    }
    get is_CFGNode() { return this.$tag === 0; }
    get dtor_id() { return this.id; }
    get dtor_seg() { return this.seg; }
    toString() {
      if (this.$tag === 0) {
        return "CFGraph.CFGNode.CFGNode" + "(" + _dafny.toString(this.id) + ", " + _dafny.toString(this.seg) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.id, other.id) && _dafny.areEqual(this.seg, other.seg);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return CFGraph.CFGNode.create_CFGNode(_dafny.Seq.of(), MiscTypes.Option.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return CFGNode.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      return CFGraph.__default.BoolsToString((_this).dtor_id);
    };
    ToDot() {
      let _this = this;
      let _934_x = CFGraph.__default.BoolSeqToNat((_this).dtor_id);
      return _dafny.Seq.Concat(_dafny.Seq.Concat(Int.__default.NatToString(_934_x), _dafny.Seq.UnicodeFromString("_")), Int.__default.NatToString(new BigNumber(((_this).dtor_id).length)));
    };
  }

  $module.BoolEdge = class BoolEdge {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_BoolEdge(src, lab, tgt) {
      let $dt = new BoolEdge(0);
      $dt.src = src;
      $dt.lab = lab;
      $dt.tgt = tgt;
      return $dt;
    }
    get is_BoolEdge() { return this.$tag === 0; }
    get dtor_src() { return this.src; }
    get dtor_lab() { return this.lab; }
    get dtor_tgt() { return this.tgt; }
    toString() {
      if (this.$tag === 0) {
        return "CFGraph.BoolEdge.BoolEdge" + "(" + _dafny.toString(this.src) + ", " + _dafny.toString(this.lab) + ", " + _dafny.toString(this.tgt) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.src, other.src) && this.lab === other.lab && _dafny.areEqual(this.tgt, other.tgt);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.Default(), false, CFGraph.CFGNode.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return BoolEdge.Default();
        }
      };
    }
    DOTPrint2() {
      let _this = this;
      let _935_lab1 = (((_this).dtor_lab) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), CFGraph.__default.jcolour), _dafny.Seq.UnicodeFromString("\">jump</FONT>"))) : (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), CFGraph.__default.skcolour), _dafny.Seq.UnicodeFromString("\">skip</FONT>"))));
      let _936_labColour = (((_this).dtor_lab) ? (CFGraph.__default.jumpColour) : (CFGraph.__default.skipColour));
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), ((_this).dtor_src).ToDot()), _dafny.Seq.UnicodeFromString(" -> s")), ((_this).dtor_tgt).ToDot()), _dafny.Seq.UnicodeFromString(" [")), _936_labColour), _dafny.Seq.UnicodeFromString("label=<")), _935_lab1), _dafny.Seq.UnicodeFromString(">]\n"));
    };
    DOTPrint(fancyExit) {
      let _this = this;
      let _937_lab1 = (((_this).dtor_lab) ? (_dafny.Seq.UnicodeFromString("tooltip=\"Jump\",style=dashed")) : (_dafny.Seq.UnicodeFromString("tooltip=\"Next\"")));
      let _938_labColour = (((_this).dtor_lab) ? (CFGraph.__default.jumpColour) : (CFGraph.__default.skipColour));
      let _939_exitPort = (((fancyExit) && ((_this).dtor_lab)) ? (_dafny.Seq.UnicodeFromString(":exit:se ")) : (_dafny.Seq.UnicodeFromString("")));
      let _940_entryPort = (((fancyExit) && ((_this).dtor_lab)) ? (_dafny.Seq.UnicodeFromString(":entry:w ")) : (_dafny.Seq.UnicodeFromString("")));
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), ((_this).dtor_src).ToDot()), _939_exitPort), _dafny.Seq.UnicodeFromString(" -> s")), ((_this).dtor_tgt).ToDot()), _940_entryPort), _dafny.Seq.UnicodeFromString(" [")), _937_lab1), _dafny.Seq.UnicodeFromString("]\n"));
    };
  }

  $module.BoolCFGraph = class BoolCFGraph {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_BoolCFGraph(edges, maxSegNum) {
      let $dt = new BoolCFGraph(0);
      $dt.edges = edges;
      $dt.maxSegNum = maxSegNum;
      return $dt;
    }
    get is_BoolCFGraph() { return this.$tag === 0; }
    get dtor_edges() { return this.edges; }
    get dtor_maxSegNum() { return this.maxSegNum; }
    toString() {
      if (this.$tag === 0) {
        return "CFGraph.BoolCFGraph.BoolCFGraph" + "(" + _dafny.toString(this.edges) + ", " + _dafny.toString(this.maxSegNum) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.edges, other.edges) && _dafny.areEqual(this.maxSegNum, other.maxSegNum);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(), _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return BoolCFGraph.Default();
        }
      };
    }
    AddEdge(e) {
      let _this = this;
      return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.Concat(_dafny.Seq.of(e), (_this).dtor_edges), _dafny.ZERO);
    };
    IsValid() {
      let _this = this;
      return (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((_this).dtor_edges).length)), true, function (_forall_var_10) {
        let _941_k = _forall_var_10;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_941_k)) && ((_941_k).isLessThan(new BigNumber(((_this).dtor_edges).length)))) || (!((((((_this).dtor_edges)[_941_k]).dtor_src).dtor_seg).is_Some) || (((((((_this).dtor_edges)[_941_k]).dtor_src).dtor_seg).dtor_v).isLessThanOrEqualTo((_this).dtor_maxSegNum)));
      })) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((_this).dtor_edges).length)), true, function (_forall_var_11) {
        let _942_k = _forall_var_11;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_942_k)) && ((_942_k).isLessThan(new BigNumber(((_this).dtor_edges).length)))) || (!((((((_this).dtor_edges)[_942_k]).dtor_tgt).dtor_seg).is_Some) || (((((((_this).dtor_edges)[_942_k]).dtor_tgt).dtor_seg).dtor_v).isLessThanOrEqualTo((_this).dtor_maxSegNum)));
      }));
    };
    Minimise() {
      let _this = this;
      let _943_r = CFGraph.__default.EdgesToMap((_this).dtor_edges, _dafny.Map.Empty.slice().updateUnsafe(CFGraph.CFGNode.create_CFGNode(_dafny.Seq.of(), MiscTypes.Option.create_Some(_dafny.ZERO)),_dafny.ZERO), _dafny.Map.Empty.slice().updateUnsafe(_dafny.ZERO,CFGraph.CFGNode.create_CFGNode(_dafny.Seq.of(), MiscTypes.Option.create_Some(_dafny.ZERO))), _dafny.Map.Empty.slice(), _dafny.ZERO, _dafny.ZERO);
      let _944_idToNum = (_943_r)[2];
      let _945_numToCFGNode = (_943_r)[3];
      let _946_lastStateNum = (_943_r)[0];
      let _947_transitions = (_943_r)[1];
      let _948_a = Automata.Auto.create_Auto((_946_lastStateNum).plus(_dafny.ONE), _947_transitions);
      if ((_dafny.ZERO).isLessThan(_946_lastStateNum)) {
        let _949_s = function () {
          let _coll1 = new _dafny.Set();
          for (const _compr_1 of _dafny.IntegerRange(_dafny.ZERO, (_946_lastStateNum).plus(_dafny.ONE))) {
            let _950_q = _compr_1;
            if (((_dafny.ZERO).isLessThanOrEqualTo(_950_q)) && ((_950_q).isLessThan((_946_lastStateNum).plus(_dafny.ONE)))) {
              _coll1.add(_950_q);
            }
          }
          return _coll1;
        }();
        let _951_p = PartitionMod.Partition.create_Partition((_946_lastStateNum).plus(_dafny.ONE), _dafny.Seq.of(_949_s));
        let _952_p1 = CFGraph.__default.SegNumPartition(_951_p, _945_numToCFGNode, (_this).dtor_maxSegNum, _dafny.ZERO);
        let _953_vp = Minimiser.Pair.create_Pair(_948_a, _952_p1);
        let _954_minim = Minimiser.__default.Minimise(_953_vp);
        let _955_listOfEdges = (_954_minim).GenerateReducedTailRec(_dafny.ZERO, _dafny.Seq.of());
        let _956_x = CFGraph.__default.NatBoolEdgesToCFGEdges(_955_listOfEdges, _945_numToCFGNode, (_this).dtor_maxSegNum);
        let _957_miniCFG = CFGraph.BoolCFGraph.create_BoolCFGraph(_956_x, (_this).dtor_maxSegNum);
        return _957_miniCFG;
      } else {
        return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(), (_this).dtor_maxSegNum);
      }
    };
    DOTPrintEdges(xe, fancyExits) {
      let _this = this;
      let _958___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xe).length))) {
          _958___accumulator = _dafny.Seq.Concat(_958___accumulator, ((xe)[_dafny.ZERO]).DOTPrint(false));
          let _in125 = _this;
          let _in126 = (xe).slice(_dafny.ONE);
          let _in127 = fancyExits;
          _this = _in125;
          ;
          xe = _in126;
          fancyExits = _in127;
          continue TAIL_CALL_START;
        } else {
          return _dafny.Seq.Concat(_958___accumulator, _dafny.Seq.UnicodeFromString(""));
        }
      }
    };
    DOTPrintNodes(xs, simpleOutput, g, printed) {
      let _this = this;
      let _959___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((g).length))) {
          let _960_srctxt = (((printed).contains(((g)[_dafny.ZERO]).dtor_src)) ? (_dafny.Seq.UnicodeFromString("")) : (((((((g)[_dafny.ZERO]).dtor_src).dtor_seg).is_None) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), (((g)[_dafny.ZERO]).dtor_src).ToDot()), _dafny.Seq.UnicodeFromString("[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) : ((_this).DOTPrintNodeLabel(((g)[_dafny.ZERO]).dtor_src, (xs)[((((g)[_dafny.ZERO]).dtor_src).dtor_seg).dtor_v], simpleOutput)))));
          let _961_tgttxt = (((printed).contains(((g)[_dafny.ZERO]).dtor_tgt)) ? (_dafny.Seq.UnicodeFromString("")) : (((((((g)[_dafny.ZERO]).dtor_tgt).dtor_seg).is_None) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), (((g)[_dafny.ZERO]).dtor_tgt).ToDot()), _dafny.Seq.UnicodeFromString("[label=<ErrorEnd <BR ALIGN=\"CENTER\"/>>]\n"))) : ((_this).DOTPrintNodeLabel(((g)[_dafny.ZERO]).dtor_tgt, (xs)[((((g)[_dafny.ZERO]).dtor_tgt).dtor_seg).dtor_v], simpleOutput)))));
          _959___accumulator = _dafny.Seq.Concat(_959___accumulator, _dafny.Seq.Concat(_960_srctxt, _961_tgttxt));
          let _in128 = _this;
          let _in129 = xs;
          let _in130 = simpleOutput;
          let _in131 = (g).slice(_dafny.ONE);
          let _in132 = (printed).Union(_dafny.Set.fromElements(((g)[_dafny.ZERO]).dtor_src, ((g)[_dafny.ZERO]).dtor_tgt));
          _this = _in128;
          ;
          xs = _in129;
          simpleOutput = _in130;
          g = _in131;
          printed = _in132;
          continue TAIL_CALL_START;
        } else {
          return _dafny.Seq.Concat(_959___accumulator, _dafny.Seq.UnicodeFromString(""));
        }
      }
    };
    DOTPrintNodeLabel(n, s, simpleOutput) {
      let _this = this;
      if (simpleOutput) {
        let _962_lab = CFGraph.__default.DOTSeg(s, ((n).dtor_seg).dtor_v);
        let _963_nodeColour = CFGraph.__default.SegColour(s);
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), (n).ToDot()), _dafny.Seq.UnicodeFromString(" [")), _963_nodeColour), _dafny.Seq.UnicodeFromString("label=<\n")), (_962_lab)[0]), _dafny.Seq.UnicodeFromString("> ")), _dafny.Seq.UnicodeFromString("tooltip=<")), (_962_lab)[1]), _dafny.Seq.UnicodeFromString(">]\n"));
      } else {
        let _964_lab = CFGraph.__default.DOTSegTable(s, ((n).dtor_seg).dtor_v);
        let _965_nodeColour = _dafny.Seq.UnicodeFromString("");
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("s"), (n).ToDot()), _dafny.Seq.UnicodeFromString(" [")), _965_nodeColour), _dafny.Seq.UnicodeFromString("label=<\n")), _964_lab), _dafny.Seq.UnicodeFromString(">]\n"));
      }
    };
    DOTPrint(xs, simpleOutput, fancyExits) {
      let _this = this;
      let _966_prefix = _dafny.Seq.UnicodeFromString("digraph CFG {\nnode [shape=box]\nnode[fontname=arial]\nedge[fontname=arial]\nranking=TB\n ");
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_966_prefix, (_this).DOTPrintNodes(xs, simpleOutput, (_this).dtor_edges, _dafny.Set.fromElements())), (_this).DOTPrintEdges((_this).dtor_edges, fancyExits)), _dafny.Seq.UnicodeFromString("}\n"));
    };
  }
  return $module;
})(); // end of module CFGraph
let LoopResolver = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "LoopResolver._default";
    }
    _parentTraits() {
      return [];
    }
    static FindFirstNodeWithPC(xs, pc, s, index) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(index)) {
          return MiscTypes.Option.create_None();
        } else if (((((s)[index]).dtor_seg).is_Some) && ((((xs)[(((s)[index]).dtor_seg).dtor_v]).StartAddress()).isEqualTo(pc))) {
          return MiscTypes.Option.create_Some(_dafny.Tuple.of((s)[index], index));
        } else {
          let _in133 = xs;
          let _in134 = pc;
          let _in135 = s;
          let _in136 = (index).plus(_dafny.ONE);
          xs = _in133;
          pc = _in134;
          s = _in135;
          index = _in136;
          continue TAIL_CALL_START;
        }
      }
    };
    static SafeLoopFound(xs, pc, seenOnPath, boolPath) {
      TAIL_CALL_START: while (true) {
        let _source69 = LoopResolver.__default.FindFirstNodeWithPC(xs, pc, seenOnPath, _dafny.ZERO);
        if (_source69.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _967___mcc_h0 = (_source69).v;
          let _968_v = _967___mcc_h0;
          let _969_init = (seenOnPath)[(_968_v)[1]];
          let _970_path = (seenOnPath).slice((_968_v)[1]);
          let _971_segs = LoopResolver.__default.NodesToSeg(_970_path);
          let _972_tgtCond = ((xs)[(((seenOnPath)[(new BigNumber((seenOnPath).length)).minus(_dafny.ONE)]).dtor_seg).dtor_v]).LeadsTo(pc, (boolPath)[(new BigNumber((boolPath).length)).minus(_dafny.ONE)]);
          let _973_w1 = LinSegments.__default.WPreSeqSegs(_971_segs, (boolPath).slice((_968_v)[1]), _972_tgtCond, xs, pc);
          if ((_973_w1).is_StTrue) {
            return MiscTypes.Option.create_Some((_968_v)[0]);
          } else if ((_973_w1).is_StFalse) {
            return MiscTypes.Option.create_None();
          } else if (LoopResolver.__default.PreservesCond(_973_w1, _971_segs, (boolPath).slice((_968_v)[1]), xs)) {
            return MiscTypes.Option.create_Some((_968_v)[0]);
          } else if (((_dafny.ZERO).isLessThan(new BigNumber(((seenOnPath).slice((_968_v)[1], new BigNumber((seenOnPath).length))).length))) && ((new BigNumber(((seenOnPath).slice((_968_v)[1], new BigNumber((seenOnPath).length))).length)).isLessThan(new BigNumber((seenOnPath).length)))) {
            let _in137 = xs;
            let _in138 = pc;
            let _in139 = (seenOnPath).slice((_968_v)[1], new BigNumber((seenOnPath).length));
            let _in140 = (boolPath).slice((_968_v)[1], new BigNumber((boolPath).length));
            xs = _in137;
            pc = _in138;
            seenOnPath = _in139;
            boolPath = _in140;
            continue TAIL_CALL_START;
          } else {
            return MiscTypes.Option.create_None();
          }
        }
      }
    };
    static PreservesCond(c, seg, exits, xs) {
      let _974_initState = State.__default.BuildInitState(c, _dafny.ZERO);
      let _975_endState = LoopResolver.__default.RunAll(seg, exits, xs, _974_initState);
      if ((_975_endState).is_EState) {
        return (_975_endState).Sat(c);
      } else {
        return false;
      }
    };
    static RunAll(seg, exits, xs, s) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((seg).length)).isEqualTo(_dafny.ZERO)) {
          return s;
        } else {
          let _source70 = ((xs)[(seg)[_dafny.ZERO]]).Run(s, (exits)[_dafny.ZERO]);
          if (_source70.is_EState) {
            let _976___mcc_h0 = (_source70).pc;
            let _977___mcc_h1 = (_source70).stack;
            let _978_st = _977___mcc_h1;
            let _979_p = _976___mcc_h0;
            let _in141 = (seg).slice(_dafny.ONE);
            let _in142 = (exits).slice(_dafny.ONE);
            let _in143 = xs;
            let _in144 = State.AState.create_EState(_979_p, _978_st);
            seg = _in141;
            exits = _in142;
            xs = _in143;
            s = _in144;
            continue TAIL_CALL_START;
          } else {
            let _980___mcc_h2 = (_source70).msg;
            let _981_m = _980___mcc_h2;
            return State.AState.create_Error(_981_m);
          }
        }
      }
    };
    static NodesToSeg(xn) {
      let _982___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xn).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_982___accumulator, _dafny.Seq.of());
        } else {
          _982___accumulator = _dafny.Seq.Concat(_982___accumulator, _dafny.Seq.of((((xn)[_dafny.ZERO]).dtor_seg).dtor_v));
          let _in145 = (xn).slice(_dafny.ONE);
          xn = _in145;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module LoopResolver
let BuildCFGraph = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "BuildCFGraph._default";
    }
    _parentTraits() {
      return [];
    }
    static BuildCFGV4(xs, maxDepth, numSeg, s, seen, seenPCs, path) {
      let _pat_let_tv2 = xs;
      let _pat_let_tv3 = path;
      let _pat_let_tv4 = numSeg;
      let _pat_let_tv5 = path;
      let _pat_let_tv6 = xs;
      let _pat_let_tv7 = maxDepth;
      let _pat_let_tv8 = seen;
      let _pat_let_tv9 = seenPCs;
      let _pat_let_tv10 = path;
      let _pat_let_tv11 = path;
      let _pat_let_tv12 = numSeg;
      let _pat_let_tv13 = path;
      let _pat_let_tv14 = path;
      let _pat_let_tv15 = numSeg;
      let _pat_let_tv16 = path;
      let _pat_let_tv17 = xs;
      let _pat_let_tv18 = path;
      let _pat_let_tv19 = numSeg;
      let _pat_let_tv20 = path;
      let _pat_let_tv21 = xs;
      let _pat_let_tv22 = maxDepth;
      let _pat_let_tv23 = seen;
      let _pat_let_tv24 = seenPCs;
      let _pat_let_tv25 = path;
      let _pat_let_tv26 = path;
      let _pat_let_tv27 = numSeg;
      let _pat_let_tv28 = path;
      let _pat_let_tv29 = xs;
      let _pat_let_tv30 = maxDepth;
      let _pat_let_tv31 = seen;
      let _pat_let_tv32 = seenPCs;
      let _pat_let_tv33 = path;
      let _pat_let_tv34 = path;
      let _pat_let_tv35 = numSeg;
      let _pat_let_tv36 = xs;
      let _pat_let_tv37 = xs;
      let _pat_let_tv38 = seen;
      let _pat_let_tv39 = path;
      let _pat_let_tv40 = seenPCs;
      let _pat_let_tv41 = path;
      let _pat_let_tv42 = numSeg;
      let _pat_let_tv43 = path;
      let _pat_let_tv44 = path;
      let _pat_let_tv45 = numSeg;
      let _pat_let_tv46 = path;
      if ((!(((xs)[numSeg]).HasExit(false))) && (!(((xs)[numSeg]).HasExit(true)))) {
        return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(), _dafny.ZERO);
      } else if ((maxDepth).isEqualTo(_dafny.ZERO)) {
        return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(path, MiscTypes.Option.create_Some(numSeg)), true, CFGraph.CFGNode.create_CFGNode(path, MiscTypes.Option.create_Some(numSeg)))), (new BigNumber((xs).length)).minus(_dafny.ONE));
      } else {
        let _983_leftBranch = ((((xs)[numSeg]).HasExit(false)) ? (function (_pat_let18_0) {
          return function (_984_leftSucc) {
            return ((((_984_leftSucc).is_EState) && (((_984_leftSucc).PC()).isLessThan(Int.__default.TWO__256))) ? (function (_pat_let19_0) {
              return function (_985_nextSeg) {
                return (((_985_nextSeg).is_Some) ? (function (_pat_let20_0) {
                  return function (_986_src) {
                    return function (_pat_let21_0) {
                      return function (_987_tgt) {
                        return function (_pat_let22_0) {
                          return function (_988_gleft) {
                            return (_988_gleft).AddEdge(CFGraph.BoolEdge.create_BoolEdge(_986_src, false, _987_tgt));
                          }(_pat_let22_0);
                        }(BuildCFGraph.__default.BuildCFGV4(_pat_let_tv6, (_pat_let_tv7).minus(_dafny.ONE), (_985_nextSeg).dtor_v, _984_leftSucc, _dafny.Seq.Concat(_pat_let_tv8, _dafny.Seq.of(_987_tgt)), _dafny.Seq.Concat(_pat_let_tv9, _dafny.Seq.of((_984_leftSucc).PC())), _dafny.Seq.Concat(_pat_let_tv10, _dafny.Seq.of(false))));
                      }(_pat_let21_0);
                    }(CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv5, _dafny.Seq.of(false)), _985_nextSeg));
                  }(_pat_let20_0);
                }(CFGraph.CFGNode.create_CFGNode(_pat_let_tv3, MiscTypes.Option.create_Some(_pat_let_tv4)))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(_pat_let_tv11, MiscTypes.Option.create_Some(_pat_let_tv12)), false, CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv13, _dafny.Seq.of(false)), MiscTypes.Option.create_None()))), _dafny.ZERO)));
              }(_pat_let19_0);
            }(LinSegments.__default.PCToSeg(_pat_let_tv2, (_984_leftSucc).PC(), _dafny.ZERO))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(_pat_let_tv14, MiscTypes.Option.create_Some(_pat_let_tv15)), false, CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv16, _dafny.Seq.of(false)), MiscTypes.Option.create_None()))), _dafny.ZERO)));
          }(_pat_let18_0);
        }(((xs)[numSeg]).Run(s, false))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(), _dafny.ZERO)));
        let _989_rightBranch = ((((xs)[numSeg]).HasExit(true)) ? (function (_pat_let23_0) {
          return function (_990_rightSucc) {
            return ((((_990_rightSucc).is_EState) && (((_990_rightSucc).PC()).isLessThan(Int.__default.TWO__256))) ? (function (_pat_let24_0) {
              return function (_991_nextSeg) {
                return (((_991_nextSeg).is_Some) ? (((!_dafny.Seq.contains(_pat_let_tv40, (_990_rightSucc).PC())) ? (function (_pat_let25_0) {
                  return function (_992_src) {
                    return function (_pat_let26_0) {
                      return function (_993_tgt) {
                        return function (_pat_let27_0) {
                          return function (_994_gright) {
                            return (_994_gright).AddEdge(CFGraph.BoolEdge.create_BoolEdge(_992_src, true, _993_tgt));
                          }(_pat_let27_0);
                        }(BuildCFGraph.__default.BuildCFGV4(_pat_let_tv21, (_pat_let_tv22).minus(_dafny.ONE), (_991_nextSeg).dtor_v, _990_rightSucc, _dafny.Seq.Concat(_pat_let_tv23, _dafny.Seq.of(_993_tgt)), _dafny.Seq.Concat(_pat_let_tv24, _dafny.Seq.of((_990_rightSucc).PC())), _dafny.Seq.Concat(_pat_let_tv25, _dafny.Seq.of(true))));
                      }(_pat_let26_0);
                    }(CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv20, _dafny.Seq.of(true)), _991_nextSeg));
                  }(_pat_let25_0);
                }(CFGraph.CFGNode.create_CFGNode(_pat_let_tv18, MiscTypes.Option.create_Some(_pat_let_tv19)))) : (function (_source71) {
                  if (_source71.is_None) {
                    return function (_pat_let28_0) {
                      return function (_995_src) {
                        return function (_pat_let29_0) {
                          return function (_996_tgt) {
                            return function (_pat_let30_0) {
                              return function (_997_gright) {
                                return (_997_gright).AddEdge(CFGraph.BoolEdge.create_BoolEdge(_995_src, true, _996_tgt));
                              }(_pat_let30_0);
                            }(BuildCFGraph.__default.BuildCFGV4(_pat_let_tv29, (_pat_let_tv30).minus(_dafny.ONE), (_991_nextSeg).dtor_v, _990_rightSucc, _dafny.Seq.Concat(_pat_let_tv31, _dafny.Seq.of(_996_tgt)), _dafny.Seq.Concat(_pat_let_tv32, _dafny.Seq.of((_990_rightSucc).PC())), _dafny.Seq.Concat(_pat_let_tv33, _dafny.Seq.of(true))));
                          }(_pat_let29_0);
                        }(CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv28, _dafny.Seq.of(true)), _991_nextSeg));
                      }(_pat_let28_0);
                    }(CFGraph.CFGNode.create_CFGNode(_pat_let_tv26, MiscTypes.Option.create_Some(_pat_let_tv27)));
                  } else {
                    let _998___mcc_h0 = (_source71).v;
                    return function (_pat_let31_0) {
                      return function (_999_prev) {
                        return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(_pat_let_tv34, MiscTypes.Option.create_Some(_pat_let_tv35)), true, _999_prev)), new BigNumber((_pat_let_tv36).length));
                      }(_pat_let31_0);
                    }(_998___mcc_h0);
                  }
                }(LoopResolver.__default.SafeLoopFound(_pat_let_tv37, (_990_rightSucc).PC(), _pat_let_tv38, _dafny.Seq.Concat(_pat_let_tv39, _dafny.Seq.of(true))))))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(_pat_let_tv41, MiscTypes.Option.create_Some(_pat_let_tv42)), true, CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv43, _dafny.Seq.of(true)), MiscTypes.Option.create_None()))), _dafny.ZERO)));
              }(_pat_let24_0);
            }(LinSegments.__default.PCToSeg(_pat_let_tv17, (_990_rightSucc).PC(), _dafny.ZERO))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(CFGraph.BoolEdge.create_BoolEdge(CFGraph.CFGNode.create_CFGNode(_pat_let_tv44, MiscTypes.Option.create_Some(_pat_let_tv45)), true, CFGraph.CFGNode.create_CFGNode(_dafny.Seq.Concat(_pat_let_tv46, _dafny.Seq.of(true)), MiscTypes.Option.create_None()))), _dafny.ZERO)));
          }(_pat_let23_0);
        }(((xs)[numSeg]).Run(s, true))) : (CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.of(), _dafny.ZERO)));
        return CFGraph.BoolCFGraph.create_BoolCFGraph(_dafny.Seq.Concat((_983_leftBranch).dtor_edges, (_989_rightBranch).dtor_edges), (new BigNumber((xs).length)).minus(_dafny.ONE));
      }
    };
  };
  return $module;
})(); // end of module BuildCFGraph
let Driver = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Driver._default";
    }
    _parentTraits() {
      return [];
    }
    static Main(args) {
      let _1000_optionParser;
      let _nw1 = new ArgParser.ArgumentParser();
      _nw1.__ctor(_dafny.Seq.UnicodeFromString("<string>"));
      _1000_optionParser = _nw1;
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-d"), _dafny.Seq.UnicodeFromString("--dis"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Disassemble <string>"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-p"), _dafny.Seq.UnicodeFromString("--proof"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Generate proof object for <string>"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-s"), _dafny.Seq.UnicodeFromString("--segment"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Print segment of <string>"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-a"), _dafny.Seq.UnicodeFromString("--all"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Same as -d -p"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-l"), _dafny.Seq.UnicodeFromString("--lib"), _dafny.ONE, _dafny.Seq.UnicodeFromString("The path to the Dafny-EVM source code. Used to add includes files in the proof object. "));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-c"), _dafny.Seq.UnicodeFromString("--cfg"), _dafny.ONE, _dafny.Seq.UnicodeFromString("Max depth. Control flow graph in DOT format"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-r"), _dafny.Seq.UnicodeFromString("--raw"), _dafny.ONE, _dafny.Seq.UnicodeFromString("Display non-minimised and minimised CFGs"));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-f"), _dafny.Seq.UnicodeFromString("--fancy"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Use exit and entry ports in segments do draw arrows (apply minimised only)."));
      (_1000_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-n"), _dafny.Seq.UnicodeFromString("--notable"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Don't use tables to pretty-print DOT file. Reduces size of the DOT file."));
      if (((new BigNumber((args).length)).isLessThan(new BigNumber(2))) || (_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("--help")))) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("Not enough arguments\n")).toVerbatimString(false));
        (_1000_optionParser).PrintHelp();
      } else if ((new BigNumber((args).length)).isEqualTo(new BigNumber(2))) {
        let _1001_x;
        _1001_x = BinaryDecoder.__default.Disassemble((args)[_dafny.ONE], _dafny.Seq.of(), _dafny.ZERO);
        PrettyPrinters.__default.PrintInstructions(_1001_x);
      } else if ((_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("--help"))) || (_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("-h")))) {
        (_1000_optionParser).PrintHelp();
      } else {
        let _1002_stringToProcess;
        _1002_stringToProcess = (args)[(new BigNumber((args).length)).minus(_dafny.ONE)];
        let _1003_optArgs;
        _1003_optArgs = (args).slice(_dafny.ONE, (new BigNumber((args).length)).minus(_dafny.ONE));
        let _1004_x;
        _1004_x = BinaryDecoder.__default.Disassemble(_1002_stringToProcess, _dafny.Seq.of(), _dafny.ZERO);
        let _source72 = (_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--dis"), _1003_optArgs);
        if (_source72.is_Success) {
          let _1005___mcc_h0 = (_source72).v;
          PrettyPrinters.__default.PrintInstructions(_1004_x);
        } else {
          let _1006___mcc_h1 = (_source72).msg;
        }
        let _source73 = (_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--segment"), _1003_optArgs);
        if (_source73.is_Success) {
          let _1007___mcc_h2 = (_source73).v;
          process.stdout.write((_dafny.Seq.UnicodeFromString("Segments:\n")).toVerbatimString(false));
          let _1008_y;
          _1008_y = Splitter.__default.SplitUpToTerminal(_1004_x, _dafny.Seq.of(), _dafny.Seq.of());
          PrettyPrinters.__default.PrintSegments(_1008_y, _dafny.ZERO);
        } else {
          let _1009___mcc_h3 = (_source73).msg;
        }
        let _source74 = (_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--proof"), _1003_optArgs);
        if (_source74.is_Success) {
          let _1010___mcc_h4 = (_source74).v;
          let _1011_pathToDafnyLib;
          _1011_pathToDafnyLib = function (_source75) {
            if (_source75.is_Success) {
              let _1012___mcc_h6 = (_source75).v;
              return function (_pat_let32_0) {
                return function (_1013_p) {
                  return (_1013_p)[_dafny.ZERO];
                }(_pat_let32_0);
              }(_1012___mcc_h6);
            } else {
              let _1014___mcc_h7 = (_source75).msg;
              return _dafny.Seq.UnicodeFromString("");
            }
          }((_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--lib"), _1003_optArgs));
          let _1015_y;
          _1015_y = Splitter.__default.SplitUpToTerminal(_1004_x, _dafny.Seq.of(), _dafny.Seq.of());
          let _1016_z;
          _1016_z = ProofObjectBuilder.__default.BuildProofObject(_1015_y);
          PrettyPrinters.__default.PrintProofObjectToDafny(_1016_z, _1011_pathToDafnyLib);
        } else {
          let _1017___mcc_h5 = (_source74).msg;
        }
        let _source76 = (_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--all"), _1003_optArgs);
        if (_source76.is_Success) {
          let _1018___mcc_h8 = (_source76).v;
          PrettyPrinters.__default.PrintInstructions(_1004_x);
          let _1019_pathToDafnyLib;
          _1019_pathToDafnyLib = function (_source77) {
            if (_source77.is_Success) {
              let _1020___mcc_h10 = (_source77).v;
              return function (_pat_let33_0) {
                return function (_1021_p) {
                  return (_1021_p)[_dafny.ZERO];
                }(_pat_let33_0);
              }(_1020___mcc_h10);
            } else {
              let _1022___mcc_h11 = (_source77).msg;
              return _dafny.Seq.UnicodeFromString("");
            }
          }((_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--lib"), _1003_optArgs));
          let _1023_y;
          _1023_y = Splitter.__default.SplitUpToTerminal(_1004_x, _dafny.Seq.of(), _dafny.Seq.of());
          let _1024_z;
          _1024_z = ProofObjectBuilder.__default.BuildProofObject(_1023_y);
          PrettyPrinters.__default.PrintProofObjectToDafny(_1024_z, _1019_pathToDafnyLib);
        } else {
          let _1025___mcc_h9 = (_source76).msg;
        }
        let _source78 = (_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--cfg"), _1003_optArgs);
        if (_source78.is_Success) {
          let _1026___mcc_h12 = (_source78).v;
          let _1027_m = _1026___mcc_h12;
          process.stdout.write((_dafny.Seq.UnicodeFromString("CFG:\n")).toVerbatimString(false));
          let _1028_y;
          _1028_y = Splitter.__default.SplitUpToTerminal(_1004_x, _dafny.Seq.of(), _dafny.Seq.of());
          if ((new BigNumber((_1028_y).length)).isEqualTo(_dafny.ZERO)) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("No segment found\n")).toVerbatimString(false));
          } else if (((new BigNumber(((_1027_m)[_dafny.ZERO]).length)).isEqualTo(_dafny.ZERO)) || (!(Driver.__default.IsNatNumber((_1027_m)[_dafny.ZERO])))) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("Argument to --cfg is not a nat.\n")).toVerbatimString(false));
          } else {
            let _1029_maxDepth;
            _1029_maxDepth = Driver.__default.StringToNat((_1027_m)[_dafny.ZERO], _dafny.ZERO);
            process.stdout.write((_dafny.Seq.UnicodeFromString("maxDepth is:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(_1029_maxDepth));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            let _1030_startAddress;
            _1030_startAddress = ((_1028_y)[_dafny.ZERO]).StartAddress();
            let _pat_let_tv47 = _1030_startAddress;
            let _1031_startState;
            _1031_startState = function (_pat_let34_0) {
              return function (_1032_dt__update__tmp_h0) {
                return function (_pat_let35_0) {
                  return function (_1033_dt__update_hpc_h0) {
                    return State.AState.create_EState(_1033_dt__update_hpc_h0, (_1032_dt__update__tmp_h0).dtor_stack);
                  }(_pat_let35_0);
                }(_pat_let_tv47);
              }(_pat_let34_0);
            }(State.__default.DEFAULT__VALIDSTATE);
            if (!(((_1028_y)[_dafny.ZERO]).StartAddress()).isEqualTo(_dafny.ZERO)) {
              process.stdout.write((_dafny.Seq.UnicodeFromString("Segment 0 does not start at address 0.\n")).toVerbatimString(false));
            } else {
              let _1034_g;
              _1034_g = BuildCFGraph.__default.BuildCFGV4(_1028_y, _1029_maxDepth, _dafny.ZERO, State.__default.DEFAULT__VALIDSTATE, _dafny.Seq.of(CFGraph.CFGNode.create_CFGNode(_dafny.Seq.of(), MiscTypes.Option.create_Some(_dafny.ZERO))), _dafny.Seq.of(_dafny.ZERO), _dafny.Seq.of());
              if (((_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--raw"), _1003_optArgs)).is_Success) {
                process.stdout.write((_dafny.Seq.UnicodeFromString("Raw CFG\n")).toVerbatimString(false));
                process.stdout.write(((_1034_g).DOTPrint(_1028_y, true, false)).toVerbatimString(false));
              } else {
                let _1035_fancy;
                _1035_fancy = ((_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--fancy"), _1003_optArgs)).is_Success;
                let _1036_simple;
                _1036_simple = ((((_1000_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--notable"), _1003_optArgs)).is_Success) ? (true) : (false));
                process.stdout.write((_dafny.Seq.UnicodeFromString("Computing Minimised CFG\n")).toVerbatimString(false));
                let _1037_g_k;
                _1037_g_k = (_1034_g).Minimise();
                if (!((_1037_g_k).IsValid())) {
                  throw new _dafny.HaltException("src/dafny/Driver.dfy(142,16): " + (_dafny.Seq.UnicodeFromString("expectation violation")).toVerbatimString(false));
                }
                process.stdout.write((_dafny.Seq.UnicodeFromString("Minimised CFG\n")).toVerbatimString(false));
                process.stdout.write(((_1037_g_k).DOTPrint(_1028_y, _1036_simple, _1035_fancy)).toVerbatimString(false));
              }
            }
          }
        } else {
          let _1038___mcc_h13 = (_source78).msg;
        }
      }
      return;
    }
    static CharToDigit(c) {
      if (_dafny.areEqual(c, new _dafny.CodePoint('0'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(_dafny.ZERO);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('1'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(_dafny.ONE);
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('2'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(2));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('3'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(3));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('4'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(4));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('5'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(5));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('6'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(6));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('7'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(7));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('8'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(8));
      } else if (_dafny.areEqual(c, new _dafny.CodePoint('9'.codePointAt(0)))) {
        return MiscTypes.Option.create_Some(new BigNumber(9));
      } else {
        return MiscTypes.Option.create_None();
      }
    };
    static IsNatNumber(s) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
          return (Driver.__default.CharToDigit((s)[_dafny.ZERO])).is_Some;
        } else {
          let _source79 = Driver.__default.CharToDigit((s)[_dafny.ZERO]);
          if (_source79.is_None) {
            return false;
          } else {
            let _1039___mcc_h0 = (_source79).v;
            let _1040_v = _1039___mcc_h0;
            let _in146 = (s).slice(_dafny.ONE);
            s = _in146;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static StringToNat(s, lastVal) {
      if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
        return (Driver.__default.CharToDigit((s)[_dafny.ZERO])).dtor_v;
      } else {
        let _1041_v = (Driver.__default.CharToDigit((s)[(new BigNumber((s).length)).minus(_dafny.ONE)])).dtor_v;
        return (_1041_v).plus((new BigNumber(10)).multipliedBy(Driver.__default.StringToNat((s).slice(0, (new BigNumber((s).length)).minus(_dafny.ONE)), _dafny.ZERO)));
      }
    };
  };
  return $module;
})(); // end of module Driver
let _module = (function() {
  let $module = {};

  return $module;
})(); // end of module _module
_dafny.HandleHaltExceptions(() => Driver.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
