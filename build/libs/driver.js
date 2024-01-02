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
// Dafny program systemModulePopulator.dfy compiled into JavaScript
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
let MiscTypes = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "MiscTypes._default";
    }
    _parentTraits() {
      return [];
    }
    static Foobar(f) {
      return true;
    };
    static Last(x) {
      return (x)[(new BigNumber((x).length)).minus(_dafny.ONE)];
    };
    static Drop(x, n) {
      return (x).slice(n);
    };
    static Init(x) {
      return (x).slice(0, (new BigNumber((x).length)).minus(_dafny.ONE));
    };
    static Zip(u, v) {
      return _dafny.Seq.Create(new BigNumber((u).length), ((_0_u, _1_v) => function (_2_i) {
        return _dafny.Tuple.of((_0_u)[_2_i], (_1_v)[_2_i]);
      })(u, v));
    };
    static UnZip(x) {
      let _3_x0 = _dafny.Seq.Create(new BigNumber((x).length), ((_4_x) => function (_5_i) {
        return ((_4_x)[_5_i])[0];
      })(x));
      let _6_x1 = _dafny.Seq.Create(new BigNumber((x).length), ((_7_x) => function (_8_i) {
        return ((_7_x)[_8_i])[1];
      })(x));
      return _dafny.Tuple.of(_3_x0, _6_x1);
    };
    static Filter(u, f) {
      let _9___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((u).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_9___accumulator, _dafny.Seq.of());
        } else if ((f)((u)[_dafny.ZERO])) {
          _9___accumulator = _dafny.Seq.Concat(_9___accumulator, _dafny.Seq.of((u)[_dafny.ZERO]));
          let _in0 = (u).slice(_dafny.ONE);
          let _in1 = f;
          u = _in0;
          f = _in1;
          continue TAIL_CALL_START;
        } else {
          let _in2 = (u).slice(_dafny.ONE);
          let _in3 = f;
          u = _in2;
          f = _in3;
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
          let _in4 = (xs).slice(_dafny.ONE);
          let _in5 = f;
          xs = _in4;
          f = _in5;
          continue TAIL_CALL_START;
        }
      }
    };
    static Flatten(x) {
      let _10___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((x).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_10___accumulator, _dafny.Seq.of());
        } else {
          _10___accumulator = _dafny.Seq.Concat(_10___accumulator, (x)[_dafny.ZERO]);
          let _in6 = (x).slice(_dafny.ONE);
          x = _in6;
          continue TAIL_CALL_START;
        }
      }
    };
    static Map(t, f) {
      return _dafny.Seq.Create(new BigNumber((t).length), ((_11_f, _12_t) => function (_13_i) {
        return (_11_f)((_12_t)[_13_i]);
      })(f, t));
    };
    static MapP(t, f) {
      return _dafny.Seq.Create(new BigNumber((t).length), ((_14_f, _15_t) => function (_16_i) {
        return (_14_f)((_15_t)[_16_i]);
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

  $module.WellDefined = class WellDefined {
    constructor () {
    }
    static get Witness() {
      return function (_17_x, _18_xs) {
    return MiscTypes.Option.create_None();
  };
    }
    static get Default() {
      return MiscTypes.WellDefined.Witness;
    }
  };

  $module.WellDefined2 = class WellDefined2 {
    constructor () {
    }
    static get Witness() {
      return function (_19_x, _20_xs) {
    return MiscTypes.Option.create_None();
  };
    }
    static get Default() {
      return MiscTypes.WellDefined2.Witness;
    }
  };

  $module.Foo = class Foo {
    constructor () {
    }
    static get Witness() {
      return function (_21_x) {
    return _dafny.ZERO;
  };
    }
    static get Default() {
      return MiscTypes.Foo.Witness;
    }
  };
  return $module;
})(); // end of module MiscTypes
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
      let _22___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(10))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(Int.__default.DigitToString(n)), _22___accumulator);
        } else {
          _22___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(Int.__default.DigitToString((n).mod(new BigNumber(10)))), _22___accumulator);
          let _in10 = _dafny.EuclideanDivision(n, new BigNumber(10));
          n = _in10;
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
          return (Int.__default.CharToDigit((s)[_dafny.ZERO])).is_Some;
        } else {
          let _source0 = Int.__default.CharToDigit((s)[_dafny.ZERO]);
          if (_source0.is_None) {
            return false;
          } else {
            let _23___mcc_h0 = (_source0).v;
            let _24_v = _23___mcc_h0;
            let _in11 = (s).slice(_dafny.ONE);
            s = _in11;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static StringToNat(s, lastVal) {
      if ((new BigNumber((s).length)).isEqualTo(_dafny.ONE)) {
        return (Int.__default.CharToDigit((s)[_dafny.ZERO])).dtor_v;
      } else {
        let _25_v = (Int.__default.CharToDigit((s)[(new BigNumber((s).length)).minus(_dafny.ONE)])).dtor_v;
        return (_25_v).plus((new BigNumber(10)).multipliedBy(Int.__default.StringToNat((s).slice(0, (new BigNumber((s).length)).minus(_dafny.ONE)), _dafny.ZERO)));
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
      let _source1 = _this;
      if (_source1.is_ArithOp) {
        let _26___mcc_h0 = (_source1).name;
        let _27___mcc_h1 = (_source1).opcode;
        let _28___mcc_h2 = (_source1).minCapacity;
        let _29___mcc_h3 = (_source1).minOperands;
        let _30___mcc_h4 = (_source1).pushes;
        let _31___mcc_h5 = (_source1).pops;
        return ((((EVMConstants.__default.ADD) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SIGNEXTEND))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source1.is_CompOp) {
        let _32___mcc_h6 = (_source1).name;
        let _33___mcc_h7 = (_source1).opcode;
        let _34___mcc_h8 = (_source1).minCapacity;
        let _35___mcc_h9 = (_source1).minOperands;
        let _36___mcc_h10 = (_source1).pushes;
        let _37___mcc_h11 = (_source1).pops;
        return (((EVMConstants.__default.LT) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.ISZERO))) && (((_this).dtor_pushes).isLessThanOrEqualTo((_this).dtor_pops));
      } else if (_source1.is_BitwiseOp) {
        let _38___mcc_h12 = (_source1).name;
        let _39___mcc_h13 = (_source1).opcode;
        let _40___mcc_h14 = (_source1).minCapacity;
        let _41___mcc_h15 = (_source1).minOperands;
        let _42___mcc_h16 = (_source1).pushes;
        let _43___mcc_h17 = (_source1).pops;
        return (((EVMConstants.__default.AND) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SAR))) && (((_this).dtor_pushes).isLessThanOrEqualTo((_this).dtor_pops));
      } else if (_source1.is_KeccakOp) {
        let _44___mcc_h18 = (_source1).name;
        let _45___mcc_h19 = (_source1).opcode;
        let _46___mcc_h20 = (_source1).minCapacity;
        let _47___mcc_h21 = (_source1).minOperands;
        let _48___mcc_h22 = (_source1).pushes;
        let _49___mcc_h23 = (_source1).pops;
        return ((((_this).dtor_opcode) === (EVMConstants.__default.KECCAK256)) && (((_this).dtor_pops).isEqualTo(new BigNumber(2)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source1.is_EnvOp) {
        let _50___mcc_h24 = (_source1).name;
        let _51___mcc_h25 = (_source1).opcode;
        let _52___mcc_h26 = (_source1).minCapacity;
        let _53___mcc_h27 = (_source1).minOperands;
        let _54___mcc_h28 = (_source1).pushes;
        let _55___mcc_h29 = (_source1).pops;
        return (((EVMConstants.__default.ADDRESS) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.BASEFEE))) && (((((((_this).dtor_pushes).isEqualTo(_dafny.ONE)) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ONE)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ZERO)) && (((_this).dtor_pops).isEqualTo(new BigNumber(3))))) || ((((_this).dtor_pushes).isEqualTo(_dafny.ZERO)) && (((_this).dtor_pops).isEqualTo(new BigNumber(4)))));
      } else if (_source1.is_MemOp) {
        let _56___mcc_h30 = (_source1).name;
        let _57___mcc_h31 = (_source1).opcode;
        let _58___mcc_h32 = (_source1).minCapacity;
        let _59___mcc_h33 = (_source1).minOperands;
        let _60___mcc_h34 = (_source1).pushes;
        let _61___mcc_h35 = (_source1).pops;
        return ((((_this).dtor_opcode) === (EVMConstants.__default.MLOAD)) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || (((((EVMConstants.__default.MSTORE) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.MSTORE8))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2))));
      } else if (_source1.is_StorageOp) {
        let _62___mcc_h36 = (_source1).name;
        let _63___mcc_h37 = (_source1).opcode;
        let _64___mcc_h38 = (_source1).minCapacity;
        let _65___mcc_h39 = (_source1).minOperands;
        let _66___mcc_h40 = (_source1).pushes;
        let _67___mcc_h41 = (_source1).pops;
        return (((EVMConstants.__default.SLOAD) === ((_this).dtor_opcode)) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ONE)))) || (((((_this).dtor_opcode) === (EVMConstants.__default.SSTORE)) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(new BigNumber(2))));
      } else if (_source1.is_JumpOp) {
        let _68___mcc_h42 = (_source1).name;
        let _69___mcc_h43 = (_source1).opcode;
        let _70___mcc_h44 = (_source1).minCapacity;
        let _71___mcc_h45 = (_source1).minOperands;
        let _72___mcc_h46 = (_source1).pushes;
        let _73___mcc_h47 = (_source1).pops;
        return ((((EVMConstants.__default.JUMP) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.JUMPI))) || (((EVMConstants.__default.JUMPDEST) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.RJUMPV)))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO));
      } else if (_source1.is_RunOp) {
        let _74___mcc_h48 = (_source1).name;
        let _75___mcc_h49 = (_source1).opcode;
        let _76___mcc_h50 = (_source1).minCapacity;
        let _77___mcc_h51 = (_source1).minOperands;
        let _78___mcc_h52 = (_source1).pushes;
        let _79___mcc_h53 = (_source1).pops;
        return ((((EVMConstants.__default.PC) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.GAS))) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE));
      } else if (_source1.is_StackOp) {
        let _80___mcc_h54 = (_source1).name;
        let _81___mcc_h55 = (_source1).opcode;
        let _82___mcc_h56 = (_source1).minCapacity;
        let _83___mcc_h57 = (_source1).minOperands;
        let _84___mcc_h58 = (_source1).pushes;
        let _85___mcc_h59 = (_source1).pops;
        return ((((((_this).dtor_opcode) === (EVMConstants.__default.POP)) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo(_dafny.ONE))) || (((((EVMConstants.__default.PUSH0) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.DUP16))) && (((_this).dtor_pushes).isEqualTo(_dafny.ONE))) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO)))) || ((((EVMConstants.__default.SWAP1) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.SWAP16))) && ((((_this).dtor_pushes).isEqualTo((_this).dtor_pops)) && (((_this).dtor_pops).isEqualTo(_dafny.ZERO))));
      } else if (_source1.is_LogOp) {
        let _86___mcc_h60 = (_source1).name;
        let _87___mcc_h61 = (_source1).opcode;
        let _88___mcc_h62 = (_source1).minCapacity;
        let _89___mcc_h63 = (_source1).minOperands;
        let _90___mcc_h64 = (_source1).pushes;
        let _91___mcc_h65 = (_source1).pops;
        return ((((EVMConstants.__default.LOG0) <= ((_this).dtor_opcode)) && (((_this).dtor_opcode) <= (EVMConstants.__default.LOG4))) && (((_this).dtor_pushes).isEqualTo(_dafny.ZERO))) && (((_this).dtor_pops).isEqualTo((new BigNumber(((_this).dtor_opcode) - (EVMConstants.__default.LOG0))).plus(new BigNumber(2))));
      } else {
        let _92___mcc_h66 = (_source1).name;
        let _93___mcc_h67 = (_source1).opcode;
        let _94___mcc_h68 = (_source1).minCapacity;
        let _95___mcc_h69 = (_source1).minOperands;
        let _96___mcc_h70 = (_source1).pushes;
        let _97___mcc_h71 = (_source1).pops;
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
    IsRevertStop() {
      let _this = this;
      return (((_this).dtor_opcode) === (EVMConstants.__default.REVERT)) || (((_this).dtor_opcode) === (EVMConstants.__default.STOP));
    };
    IsReturn() {
      let _this = this;
      return ((_this).dtor_opcode) === (EVMConstants.__default.RETURN);
    };
    IsInvalid() {
      let _this = this;
      return ((_this).dtor_opcode) === (EVMConstants.__default.INVALID);
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
    static IsHexString(s) {
      return _dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber((s).length)), true, function (_forall_var_0) {
        let _98_k = _forall_var_0;
        return !(((_dafny.ZERO).isLessThanOrEqualTo(_98_k)) && ((_98_k).isLessThan(new BigNumber((s).length)))) || (Hex.__default.IsHex((s)[_98_k]));
      });
    };
    static HexToU8(s) {
      let _source2 = _dafny.Tuple.of(Hex.__default.HexVal((s)[_dafny.ZERO]), Hex.__default.HexVal((s)[_dafny.ONE]));
      let _99___mcc_h0 = (_source2)[0];
      let _100___mcc_h1 = (_source2)[1];
      let _source3 = _99___mcc_h0;
      if (_source3.is_None) {
        let _source4 = _100___mcc_h1;
        if (_source4.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _101___mcc_h2 = (_source4).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _102___mcc_h4 = (_source3).v;
        let _source5 = _100___mcc_h1;
        if (_source5.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _103___mcc_h6 = (_source5).v;
          let _104_v2 = _103___mcc_h6;
          let _105_v1 = _102___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__4).multipliedBy(new BigNumber(_105_v1))).plus(new BigNumber(_104_v2))).toNumber());
        }
      }
    };
    static HexToU16(s) {
      let _source6 = _dafny.Tuple.of(Hex.__default.HexToU8((s).slice(0, new BigNumber(2))), Hex.__default.HexToU8((s).slice(new BigNumber(2))));
      let _106___mcc_h0 = (_source6)[0];
      let _107___mcc_h1 = (_source6)[1];
      let _source7 = _106___mcc_h0;
      if (_source7.is_None) {
        let _source8 = _107___mcc_h1;
        if (_source8.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _108___mcc_h2 = (_source8).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _109___mcc_h4 = (_source7).v;
        let _source9 = _107___mcc_h1;
        if (_source9.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _110___mcc_h6 = (_source9).v;
          let _111_v2 = _110___mcc_h6;
          let _112_v1 = _109___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__8).multipliedBy(new BigNumber(_112_v1))).plus(new BigNumber(_111_v2))).toNumber());
        }
      }
    };
    static HexToU32(s) {
      let _source10 = _dafny.Tuple.of(Hex.__default.HexToU16((s).slice(0, new BigNumber(4))), Hex.__default.HexToU16((s).slice(new BigNumber(4))));
      let _113___mcc_h0 = (_source10)[0];
      let _114___mcc_h1 = (_source10)[1];
      let _source11 = _113___mcc_h0;
      if (_source11.is_None) {
        let _source12 = _114___mcc_h1;
        if (_source12.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _115___mcc_h2 = (_source12).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _116___mcc_h4 = (_source11).v;
        let _source13 = _114___mcc_h1;
        if (_source13.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _117___mcc_h6 = (_source13).v;
          let _118_v2 = _117___mcc_h6;
          let _119_v1 = _116___mcc_h4;
          return MiscTypes.Option.create_Some((((Int.__default.TWO__16).multipliedBy(new BigNumber(_119_v1))).plus(new BigNumber(_118_v2))).toNumber());
        }
      }
    };
    static HexToU64(s) {
      let _source14 = _dafny.Tuple.of(Hex.__default.HexToU32((s).slice(0, new BigNumber(8))), Hex.__default.HexToU32((s).slice(new BigNumber(8))));
      let _120___mcc_h0 = (_source14)[0];
      let _121___mcc_h1 = (_source14)[1];
      let _source15 = _120___mcc_h0;
      if (_source15.is_None) {
        let _source16 = _121___mcc_h1;
        if (_source16.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _122___mcc_h2 = (_source16).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _123___mcc_h4 = (_source15).v;
        let _source17 = _121___mcc_h1;
        if (_source17.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _124___mcc_h6 = (_source17).v;
          let _125_v2 = _124___mcc_h6;
          let _126_v1 = _123___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__32).multipliedBy(new BigNumber(_126_v1))).plus(new BigNumber(_125_v2)));
        }
      }
    };
    static HexToU128(s) {
      let _source18 = _dafny.Tuple.of(Hex.__default.HexToU64((s).slice(0, new BigNumber(16))), Hex.__default.HexToU64((s).slice(new BigNumber(16))));
      let _127___mcc_h0 = (_source18)[0];
      let _128___mcc_h1 = (_source18)[1];
      let _source19 = _127___mcc_h0;
      if (_source19.is_None) {
        let _source20 = _128___mcc_h1;
        if (_source20.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _129___mcc_h2 = (_source20).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _130___mcc_h4 = (_source19).v;
        let _source21 = _128___mcc_h1;
        if (_source21.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _131___mcc_h6 = (_source21).v;
          let _132_v2 = _131___mcc_h6;
          let _133_v1 = _130___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__64).multipliedBy(_133_v1)).plus(_132_v2));
        }
      }
    };
    static HexToU256(s) {
      let _source22 = _dafny.Tuple.of(Hex.__default.HexToU128((s).slice(0, new BigNumber(32))), Hex.__default.HexToU128((s).slice(new BigNumber(32))));
      let _134___mcc_h0 = (_source22)[0];
      let _135___mcc_h1 = (_source22)[1];
      let _source23 = _134___mcc_h0;
      if (_source23.is_None) {
        let _source24 = _135___mcc_h1;
        if (_source24.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _136___mcc_h2 = (_source24).v;
          return MiscTypes.Option.create_None();
        }
      } else {
        let _137___mcc_h4 = (_source23).v;
        let _source25 = _135___mcc_h1;
        if (_source25.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _138___mcc_h6 = (_source25).v;
          let _139_v2 = _138___mcc_h6;
          let _140_v1 = _137___mcc_h4;
          return MiscTypes.Option.create_Some(((Int.__default.TWO__128).multipliedBy(_140_v1)).plus(_139_v2));
        }
      }
    };
    static U8ToHex(n) {
      return _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex(_dafny.EuclideanDivision(new BigNumber(n), Int.__default.TWO__4))), _dafny.Seq.of(Hex.__default.DecToHex((new BigNumber(n)).mod(Int.__default.TWO__4))));
    };
    static HexHelper(s) {
      let _141___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_141___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _141___accumulator = _dafny.Seq.Concat(_141___accumulator, Hex.__default.U8ToHex((s)[_dafny.ZERO]));
          let _in12 = (s).slice(_dafny.ONE);
          s = _in12;
          continue TAIL_CALL_START;
        }
      }
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
      let _142___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(16))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex(n)), _142___accumulator);
        } else {
          _142___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(Hex.__default.DecToHex((n).mod(new BigNumber(16)))), _142___accumulator);
          let _in13 = _dafny.EuclideanDivision(n, new BigNumber(16));
          n = _in13;
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

  $module.__default = class __default {
    constructor () {
      this._tname = "StackElement._default";
    }
    _parentTraits() {
      return [];
    }
    static StackToString(s) {
      let _143___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_143___accumulator, _dafny.Seq.UnicodeFromString("Ø"));
        } else {
          _143___accumulator = _dafny.Seq.Concat(_143___accumulator, _dafny.Seq.Concat(((s)[_dafny.ZERO]).ToString(), _dafny.Seq.UnicodeFromString(",")));
          let _in14 = (s).slice(_dafny.ONE);
          s = _in14;
          continue TAIL_CALL_START;
        }
      }
    };
  };

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
      let _source26 = _this;
      if (_source26.is_Value) {
        let _144___mcc_h0 = (_source26).v;
        let _145_v = _144___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(Int.__default.NatToString(_145_v), _dafny.Seq.UnicodeFromString("(0x")), Hex.__default.NatToHex(_145_v)), _dafny.Seq.UnicodeFromString(")"));
      } else {
        let _146___mcc_h1 = (_source26).s;
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
            let _147_i = WeakPre.__default.FindVal(((c2).dtor_trackedPos)[_dafny.ZERO], (c1).dtor_trackedPos, _dafny.ZERO);
            if (_dafny.areEqual(((c1).dtor_trackedVals)[_147_i], ((c2).dtor_trackedVals)[_dafny.ZERO])) {
              return c1;
            } else {
              return WeakPre.Cond.create_StFalse();
            }
          } else {
            return WeakPre.Cond.create_StCond(_dafny.Seq.Concat((c1).dtor_trackedPos, _dafny.Seq.of(((c2).dtor_trackedPos)[_dafny.ZERO])), _dafny.Seq.Concat((c1).dtor_trackedVals, _dafny.Seq.of(((c2).dtor_trackedVals)[_dafny.ZERO])));
          }
        } else {
          if (_dafny.Seq.contains((c1).dtor_trackedPos, ((c2).dtor_trackedPos)[_dafny.ZERO])) {
            let _in15 = c1;
            let _in16 = WeakPre.Cond.create_StCond(((c2).dtor_trackedPos).slice(_dafny.ONE), ((c2).dtor_trackedVals).slice(_dafny.ONE));
            c1 = _in15;
            c2 = _in16;
            continue TAIL_CALL_START;
          } else {
            let _148_p = _dafny.Seq.Concat((c1).dtor_trackedPos, _dafny.Seq.of(((c2).dtor_trackedPos)[_dafny.ZERO]));
            let _149_v = _dafny.Seq.Concat((c1).dtor_trackedVals, _dafny.Seq.of(((c2).dtor_trackedVals)[_dafny.ZERO]));
            let _in17 = WeakPre.Cond.create_StCond(_148_p, _149_v);
            let _in18 = WeakPre.Cond.create_StCond(((c2).dtor_trackedPos).slice(_dafny.ONE), ((c2).dtor_trackedVals).slice(_dafny.ONE));
            c1 = _in17;
            c2 = _in18;
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
          let _in19 = x;
          let _in20 = xs;
          let _in21 = (index).plus(_dafny.ONE);
          x = _in19;
          xs = _in20;
          index = _in21;
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
      return !((_this).is_StCond) || ((((new BigNumber(((_this).dtor_trackedPos).length)).isEqualTo(new BigNumber(((_this).dtor_trackedVals).length))) && ((_dafny.ZERO).isLessThan(new BigNumber(((_this).dtor_trackedVals).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((_this).dtor_trackedPos).length)), true, function (_forall_var_1) {
        let _150_k = _forall_var_1;
        return _dafny.Quantifier(_dafny.IntegerRange((_150_k).plus(_dafny.ONE), new BigNumber(((_this).dtor_trackedPos).length)), true, function (_forall_var_2) {
          let _151_k_k = _forall_var_2;
          return !((((_dafny.ZERO).isLessThanOrEqualTo(_150_k)) && ((_150_k).isLessThan(_151_k_k))) && ((_151_k_k).isLessThan(new BigNumber(((_this).dtor_trackedPos).length)))) || (!(((_this).dtor_trackedPos)[_150_k]).isEqualTo(((_this).dtor_trackedPos)[_151_k_k]));
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
      let _source27 = _dafny.Tuple.of(_this, c);
      let _152___mcc_h0 = (_source27)[0];
      let _153___mcc_h1 = (_source27)[1];
      let _source28 = _152___mcc_h0;
      if (_source28.is_StTrue) {
        let _source29 = _153___mcc_h1;
        if (_source29.is_StTrue) {
          let _154_cond = _153___mcc_h1;
          return _154_cond;
        } else if (_source29.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _155___mcc_h2 = (_source29).trackedPos;
          let _156___mcc_h3 = (_source29).trackedVals;
          let _157_cond = _153___mcc_h1;
          return _157_cond;
        }
      } else if (_source28.is_StFalse) {
        let _source30 = _153___mcc_h1;
        if (_source30.is_StTrue) {
          return WeakPre.Cond.create_StFalse();
        } else if (_source30.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _158___mcc_h8 = (_source30).trackedPos;
          let _159___mcc_h9 = (_source30).trackedVals;
          return WeakPre.Cond.create_StFalse();
        }
      } else {
        let _160___mcc_h14 = (_source28).trackedPos;
        let _161___mcc_h15 = (_source28).trackedVals;
        let _source31 = _153___mcc_h1;
        if (_source31.is_StTrue) {
          let _162_c1 = _152___mcc_h0;
          return _162_c1;
        } else if (_source31.is_StFalse) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _163___mcc_h22 = (_source31).trackedPos;
          let _164___mcc_h23 = (_source31).trackedVals;
          let _165_c2 = _153___mcc_h1;
          let _166_c1 = _152___mcc_h0;
          return WeakPre.__default.Merge(_166_c1, _165_c2);
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
      let _167_dt__update__tmp_h0 = _this;
      let _168_dt__update_htrackedVals_h0 = ((_this).dtor_trackedVals).slice(_dafny.ONE);
      let _169_dt__update_htrackedPos_h0 = ((_this).dtor_trackedPos).slice(_dafny.ONE);
      return WeakPre.Cond.create_StCond(_169_dt__update_htrackedPos_h0, _168_dt__update_htrackedVals_h0);
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
          let _in22 = _this;
          let _in23 = _dafny.Seq.update(r, ((_this).dtor_trackedPos)[index], StackElement.StackElem.create_Value(((_this).dtor_trackedVals)[index]));
          let _in24 = (index).plus(_dafny.ONE);
          _this = _in22;
          ;
          r = _in23;
          index = _in24;
          continue TAIL_CALL_START;
        } else {
          let _170_suf = _dafny.Seq.Create((((_this).dtor_trackedPos)[index]).minus(new BigNumber((r).length)), function (_171___v2) {
            return StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString(""));
          });
          let _in25 = _this;
          let _in26 = _dafny.Seq.Concat(_dafny.Seq.Concat(r, _170_suf), _dafny.Seq.of(StackElement.StackElem.create_Value(((_this).dtor_trackedVals)[index])));
          let _in27 = (index).plus(_dafny.ONE);
          _this = _in25;
          ;
          r = _in26;
          index = _in27;
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
    static BuildInitState(c, initpc) {
      let _172_s0 = State.__default.DEFAULT__VALIDSTATE;
      if ((c).is_StCond) {
        let _173_dt__update__tmp_h0 = _172_s0;
        let _174_dt__update_hpc_h0 = initpc;
        let _175_dt__update_hstack_h0 = (c).BuildStack(_dafny.Seq.of(), _dafny.ZERO);
        return State.AState.create_EState(_174_dt__update_hpc_h0, _175_dt__update_hstack_h0);
      } else {
        let _176_dt__update__tmp_h1 = _172_s0;
        let _177_dt__update_hpc_h1 = initpc;
        return State.AState.create_EState(_177_dt__update_hpc_h1, (_176_dt__update__tmp_h1).dtor_stack);
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
      let _source32 = _this;
      if (_source32.is_EState) {
        let _178___mcc_h0 = (_source32).pc;
        let _179___mcc_h1 = (_source32).stack;
        let _180_stack = _179___mcc_h1;
        let _181_pc = _178___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("(pc=0x"), Hex.__default.NatToHex(_181_pc)), _dafny.Seq.UnicodeFromString(" stack:[")), StackElement.__default.StackToString(_180_stack)), _dafny.Seq.UnicodeFromString("])"));
      } else {
        let _182___mcc_h2 = (_source32).msg;
        let _183_m = _182___mcc_h2;
        return _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("ErrorState "), _183_m);
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
      let _184_dt__update__tmp_h0 = _this;
      let _185_dt__update_hpc_h0 = ((_this).dtor_pc).plus(n);
      return State.AState.create_EState(_185_dt__update_hpc_h0, (_184_dt__update__tmp_h0).dtor_stack);
    };
    Goto(tgt) {
      let _this = this;
      let _186_dt__update__tmp_h0 = _this;
      let _187_dt__update_hpc_h0 = tgt;
      return State.AState.create_EState(_187_dt__update_hpc_h0, (_186_dt__update__tmp_h0).dtor_stack);
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
      let _188_dt__update__tmp_h0 = _this;
      let _189_dt__update_hstack_h0 = ((_this).dtor_stack).slice(n);
      return State.AState.create_EState((_188_dt__update__tmp_h0).dtor_pc, _189_dt__update_hstack_h0);
    };
    Push(v) {
      let _this = this;
      let _190_dt__update__tmp_h0 = _this;
      let _191_dt__update_hstack_h0 = _dafny.Seq.Concat(_dafny.Seq.of(v), (_this).dtor_stack);
      return State.AState.create_EState((_190_dt__update__tmp_h0).dtor_pc, _191_dt__update_hstack_h0);
    };
    PushNRandom(n) {
      let _this = this;
      let _192_xr = _dafny.Seq.Create(n, function (_193___v0) {
        return StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString(""));
      });
      let _194_dt__update__tmp_h0 = _this;
      let _195_dt__update_hstack_h0 = _dafny.Seq.Concat(_192_xr, (_this).dtor_stack);
      return State.AState.create_EState((_194_dt__update__tmp_h0).dtor_pc, _195_dt__update_hstack_h0);
    };
    Dup(n) {
      let _this = this;
      let _196_nth = ((_this).dtor_stack)[(n).minus(_dafny.ONE)];
      let _197_dt__update__tmp_h0 = _this;
      let _198_dt__update_hstack_h0 = _dafny.Seq.Concat(_dafny.Seq.of(_196_nth), (_this).dtor_stack);
      return State.AState.create_EState((_197_dt__update__tmp_h0).dtor_pc, _198_dt__update_hstack_h0);
    };
    Swap(n) {
      let _this = this;
      let _199_nth = ((_this).dtor_stack)[n];
      let _200_top = ((_this).dtor_stack)[_dafny.ZERO];
      let _201_dt__update__tmp_h0 = _this;
      let _202_dt__update_hstack_h0 = _dafny.Seq.update(_dafny.Seq.update((_this).dtor_stack, _dafny.ZERO, _199_nth), n, _200_top);
      return State.AState.create_EState((_201_dt__update__tmp_h0).dtor_pc, _202_dt__update_hstack_h0);
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
      let _203_pad = _dafny.Seq.Create((new BigNumber(64)).minus(new BigNumber((xc).length)), function (_204___v149) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      });
      return (Hex.__default.HexToU256(_dafny.Seq.Concat(_203_pad, xc))).Extract();
    };
    static ToDot(xi) {
      let _205___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xi).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_205___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          _205___accumulator = _dafny.Seq.Concat(_205___accumulator, ((xi)[_dafny.ZERO]).ToHTML());
          let _in28 = (xi).slice(_dafny.ONE);
          xi = _in28;
          continue TAIL_CALL_START;
        }
      }
    };
    static Colours(i) {
      let _source33 = (i).dtor_op;
      if (_source33.is_ArithOp) {
        let _206___mcc_h0 = (_source33).name;
        let _207___mcc_h1 = (_source33).opcode;
        let _208___mcc_h2 = (_source33).minCapacity;
        let _209___mcc_h3 = (_source33).minOperands;
        let _210___mcc_h4 = (_source33).pushes;
        let _211___mcc_h5 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("#316152"), _dafny.Seq.UnicodeFromString("#c6eb76"));
      } else if (_source33.is_CompOp) {
        let _212___mcc_h6 = (_source33).name;
        let _213___mcc_h7 = (_source33).opcode;
        let _214___mcc_h8 = (_source33).minCapacity;
        let _215___mcc_h9 = (_source33).minOperands;
        let _216___mcc_h10 = (_source33).pushes;
        let _217___mcc_h11 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("darkgoldenrod"), _dafny.Seq.UnicodeFromString("bisque"));
      } else if (_source33.is_BitwiseOp) {
        let _218___mcc_h12 = (_source33).name;
        let _219___mcc_h13 = (_source33).opcode;
        let _220___mcc_h14 = (_source33).minCapacity;
        let _221___mcc_h15 = (_source33).minOperands;
        let _222___mcc_h16 = (_source33).pushes;
        let _223___mcc_h17 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("orange"), _dafny.Seq.UnicodeFromString("#f3f383"));
      } else if (_source33.is_KeccakOp) {
        let _224___mcc_h18 = (_source33).name;
        let _225___mcc_h19 = (_source33).opcode;
        let _226___mcc_h20 = (_source33).minCapacity;
        let _227___mcc_h21 = (_source33).minOperands;
        let _228___mcc_h22 = (_source33).pushes;
        let _229___mcc_h23 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("grey"), _dafny.Seq.UnicodeFromString("linen"));
      } else if (_source33.is_EnvOp) {
        let _230___mcc_h24 = (_source33).name;
        let _231___mcc_h25 = (_source33).opcode;
        let _232___mcc_h26 = (_source33).minCapacity;
        let _233___mcc_h27 = (_source33).minOperands;
        let _234___mcc_h28 = (_source33).pushes;
        let _235___mcc_h29 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("darkslategrey"), _dafny.Seq.UnicodeFromString("lightgrey"));
      } else if (_source33.is_MemOp) {
        let _236___mcc_h30 = (_source33).name;
        let _237___mcc_h31 = (_source33).opcode;
        let _238___mcc_h32 = (_source33).minCapacity;
        let _239___mcc_h33 = (_source33).minOperands;
        let _240___mcc_h34 = (_source33).pushes;
        let _241___mcc_h35 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("sienna"), _dafny.Seq.UnicodeFromString("wheat"));
      } else if (_source33.is_StorageOp) {
        let _242___mcc_h36 = (_source33).name;
        let _243___mcc_h37 = (_source33).opcode;
        let _244___mcc_h38 = (_source33).minCapacity;
        let _245___mcc_h39 = (_source33).minOperands;
        let _246___mcc_h40 = (_source33).pushes;
        let _247___mcc_h41 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("fuchsia"), _dafny.Seq.UnicodeFromString("mistyrose"));
      } else if (_source33.is_JumpOp) {
        let _248___mcc_h42 = (_source33).name;
        let _249___mcc_h43 = (_source33).opcode;
        let _250___mcc_h44 = (_source33).minCapacity;
        let _251___mcc_h45 = (_source33).minOperands;
        let _252___mcc_h46 = (_source33).pushes;
        let _253___mcc_h47 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("purple"), _dafny.Seq.UnicodeFromString("thistle"));
      } else if (_source33.is_RunOp) {
        let _254___mcc_h48 = (_source33).name;
        let _255___mcc_h49 = (_source33).opcode;
        let _256___mcc_h50 = (_source33).minCapacity;
        let _257___mcc_h51 = (_source33).minOperands;
        let _258___mcc_h52 = (_source33).pushes;
        let _259___mcc_h53 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("sienna"), _dafny.Seq.UnicodeFromString("tan"));
      } else if (_source33.is_StackOp) {
        let _260___mcc_h54 = (_source33).name;
        let _261___mcc_h55 = (_source33).opcode;
        let _262___mcc_h56 = (_source33).minCapacity;
        let _263___mcc_h57 = (_source33).minOperands;
        let _264___mcc_h58 = (_source33).pushes;
        let _265___mcc_h59 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("royalblue"), _dafny.Seq.UnicodeFromString("powderblue"));
      } else if (_source33.is_LogOp) {
        let _266___mcc_h60 = (_source33).name;
        let _267___mcc_h61 = (_source33).opcode;
        let _268___mcc_h62 = (_source33).minCapacity;
        let _269___mcc_h63 = (_source33).minOperands;
        let _270___mcc_h64 = (_source33).pushes;
        let _271___mcc_h65 = (_source33).pops;
        return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("cornflowerblue"), _dafny.Seq.UnicodeFromString("lavender"));
      } else {
        let _272___mcc_h66 = (_source33).name;
        let _273___mcc_h67 = (_source33).opcode;
        let _274___mcc_h68 = (_source33).minCapacity;
        let _275___mcc_h69 = (_source33).minOperands;
        let _276___mcc_h70 = (_source33).pushes;
        let _277___mcc_h71 = (_source33).pops;
        let _278_opcode = _273___mcc_h67;
        if (((_278_opcode) === (EVMConstants.__default.STOP)) || ((_278_opcode) === (EVMConstants.__default.REVERT))) {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("brown"), _dafny.Seq.UnicodeFromString("lightsalmon"));
        } else if ((_278_opcode) === (EVMConstants.__default.RETURN)) {
          return _dafny.Tuple.of(_dafny.Seq.UnicodeFromString("teal"), _dafny.Seq.UnicodeFromString("greenyellow"));
        } else if (((((_278_opcode) === (EVMConstants.__default.CALL)) || ((_278_opcode) === (EVMConstants.__default.CALLCODE))) || ((_278_opcode) === (EVMConstants.__default.DELEGATECALL))) || ((_278_opcode) === (EVMConstants.__default.STATICCALL))) {
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
    Size() {
      let _this = this;
      return (_dafny.ONE).plus(_dafny.EuclideanDivision(new BigNumber(((_this).dtor_arg).length), new BigNumber(2)));
    };
    ToString() {
      let _this = this;
      let _279_x = (_this).dtor_arg;
      if ((((_this).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID)) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(((_this).dtor_op).Name(), _dafny.Seq.UnicodeFromString(" ")), _279_x);
      } else {
        return _dafny.Seq.Concat(((_this).dtor_op).Name(), (((_dafny.ZERO).isLessThan(new BigNumber((_279_x).length))) ? (_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" 0x"), _279_x)) : (_dafny.Seq.UnicodeFromString(""))));
      }
    };
    Equiv(i) {
      let _this = this;
      return (_dafny.areEqual((_this).dtor_op, (i).dtor_op)) && (_dafny.areEqual((_this).dtor_arg, (i).dtor_arg));
    };
    ToHTML() {
      let _this = this;
      let _280_x = (_this).dtor_arg;
      let _281_cols = Instructions.__default.Colours(_this);
      let _282_formattedAddress = _dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber((Hex.__default.NatToHex((_this).dtor_address)).length)).mod(new BigNumber(2)), function (_283___v0) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      }), Hex.__default.NatToHex((_this).dtor_address));
      let _284_insText = (((((_this).dtor_op).dtor_opcode) === (EVMConstants.__default.INVALID)) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), (_281_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), _dafny.Seq.UnicodeFromString(" ")), _280_x)) : (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT color=\""), (_281_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), (((_dafny.ZERO).isLessThan(new BigNumber((_280_x).length))) ? (_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" 0x"), _280_x)) : (_dafny.Seq.UnicodeFromString(""))))));
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("0x"), _282_formattedAddress), _dafny.Seq.UnicodeFromString(":")), _284_insText), _dafny.Seq.UnicodeFromString(" <BR ALIGN=\"LEFT\"/>\n"));
    };
    ToHTMLTable(entryPortTag, exitPortTag) {
      let _this = this;
      let _285_cols = Instructions.__default.Colours(_this);
      let _286_formattedAddress = _dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber((Hex.__default.NatToHex((_this).dtor_address)).length)).mod(new BigNumber(2)), function (_287___v1) {
        return new _dafny.CodePoint('0'.codePointAt(0));
      }), Hex.__default.NatToHex((_this).dtor_address));
      let _288_gasLine = _dafny.Seq.UnicodeFromString("&#9981;");
      let _289_oplineTD = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" "), entryPortTag), _dafny.Seq.UnicodeFromString(">")), _dafny.Seq.UnicodeFromString("0x")), _286_formattedAddress), _dafny.Seq.UnicodeFromString(" </TD>\n")), _dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"false\" align=\"left\" cellpadding=\"1\" tooltip=\"Gas: ")), EVMToolTips.__default.Gas(((_this).dtor_op).dtor_opcode)), _dafny.Seq.UnicodeFromString(" \" ")), _dafny.Seq.UnicodeFromString("target=\"_blank\" href=\"")), EVMToolTips.__default.gasRefLine), _dafny.Seq.UnicodeFromString("\"")), _dafny.Seq.UnicodeFromString(">")), _288_gasLine), _dafny.Seq.UnicodeFromString("</TD>")), _dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"true\" style=\"Rounded\" BORDER=\"0\" BGCOLOR=\"")), (_285_cols)[1]), _dafny.Seq.UnicodeFromString("\" align=\"left\" cellpadding=\"3\" ")), exitPortTag), _dafny.Seq.UnicodeFromString(" href=\"")), EVMToolTips.__default.bytecodeRefLine), Int.__default.NatToString((EVMToolTips.__default.ToolTip(((_this).dtor_op).dtor_opcode))[1])), _dafny.Seq.UnicodeFromString("\" target=\"_blank\" ")), _dafny.Seq.UnicodeFromString(" tooltip=\"")), (EVMToolTips.__default.ToolTip(((_this).dtor_op).dtor_opcode))[0]), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString(">")), _dafny.Seq.UnicodeFromString("<FONT color=\"")), (_285_cols)[0]), _dafny.Seq.UnicodeFromString("\">")), ((_this).dtor_op).Name()), _dafny.Seq.UnicodeFromString("</FONT>")), _dafny.Seq.UnicodeFromString("</TD>"));
      let _290_arglineTD = (((_dafny.ZERO).isLessThan(new BigNumber(((_this).dtor_arg).length))) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TD width=\"1\" fixedsize=\"true\" align=\"left\">"), _dafny.Seq.UnicodeFromString("  0x")), (_this).dtor_arg), _dafny.Seq.UnicodeFromString("</TD>"))) : (_dafny.Seq.UnicodeFromString("")));
      let _291_lineTR = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TR>"), _289_oplineTD), _290_arglineTD), _dafny.Seq.UnicodeFromString("</TR>"));
      let _292_itemTable = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TABLE  border=\"0\" cellpadding=\"0\" cellborder=\"0\" CELLSPACING=\"1\">"), _291_lineTR), _dafny.Seq.UnicodeFromString("</TABLE>"));
      return _292_itemTable;
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
      let _source34 = (_this).dtor_op;
      if (_source34.is_ArithOp) {
        let _293___mcc_h0 = (_source34).name;
        let _294___mcc_h1 = (_source34).opcode;
        let _295___mcc_h2 = (_source34).minCapacity;
        let _296___mcc_h3 = (_source34).minOperands;
        let _297___mcc_h4 = (_source34).pushes;
        let _298___mcc_h5 = (_source34).pops;
        let _299_pops = _298___mcc_h5;
        let _300_pushes = _297___mcc_h4;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Arithmetic operator with target 0")));
        }
      } else if (_source34.is_CompOp) {
        let _301___mcc_h6 = (_source34).name;
        let _302___mcc_h7 = (_source34).opcode;
        let _303___mcc_h8 = (_source34).minCapacity;
        let _304___mcc_h9 = (_source34).minOperands;
        let _305___mcc_h10 = (_source34).pushes;
        let _306___mcc_h11 = (_source34).pops;
        let _307_pops = _306___mcc_h11;
        let _308_pushes = _305___mcc_h10;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right(((pos_k).plus(_307_pops)).minus(_308_pushes));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Comparison operator with target 0")));
        }
      } else if (_source34.is_BitwiseOp) {
        let _309___mcc_h12 = (_source34).name;
        let _310___mcc_h13 = (_source34).opcode;
        let _311___mcc_h14 = (_source34).minCapacity;
        let _312___mcc_h15 = (_source34).minOperands;
        let _313___mcc_h16 = (_source34).pushes;
        let _314___mcc_h17 = (_source34).pops;
        let _315_pops = _314___mcc_h17;
        let _316_pushes = _313___mcc_h16;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right(((pos_k).plus(_315_pops)).minus(_316_pushes));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Bitwise operator with target 0")));
        }
      } else if (_source34.is_KeccakOp) {
        let _317___mcc_h18 = (_source34).name;
        let _318___mcc_h19 = (_source34).opcode;
        let _319___mcc_h20 = (_source34).minCapacity;
        let _320___mcc_h21 = (_source34).minOperands;
        let _321___mcc_h22 = (_source34).pushes;
        let _322___mcc_h23 = (_source34).pops;
        let _323_pops = _322___mcc_h23;
        let _324_pushes = _321___mcc_h22;
        if ((_dafny.ONE).isLessThanOrEqualTo(pos_k)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Keccak operator with target 0")));
        }
      } else if (_source34.is_EnvOp) {
        let _325___mcc_h24 = (_source34).name;
        let _326___mcc_h25 = (_source34).opcode;
        let _327___mcc_h26 = (_source34).minCapacity;
        let _328___mcc_h27 = (_source34).minOperands;
        let _329___mcc_h28 = (_source34).pushes;
        let _330___mcc_h29 = (_source34).pops;
        let _331_pops = _330___mcc_h29;
        let _332_pushes = _329___mcc_h28;
        if (((_332_pushes).isEqualTo(_dafny.ONE)) && ((_331_pops).isEqualTo(_dafny.ZERO))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Env operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
          }
        } else if (((_332_pushes).isEqualTo(_dafny.ONE)) && ((_331_pops).isEqualTo(_dafny.ONE))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Env operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        } else {
          return MiscTypes.Either.create_Right(((pos_k).plus(_331_pops)).minus(_332_pushes));
        }
      } else if (_source34.is_MemOp) {
        let _333___mcc_h30 = (_source34).name;
        let _334___mcc_h31 = (_source34).opcode;
        let _335___mcc_h32 = (_source34).minCapacity;
        let _336___mcc_h33 = (_source34).minOperands;
        let _337___mcc_h34 = (_source34).pushes;
        let _338___mcc_h35 = (_source34).pops;
        let _339_pops = _338___mcc_h35;
        let _340_pushes = _337___mcc_h34;
        if ((_340_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(2)));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Mem operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        }
      } else if (_source34.is_StorageOp) {
        let _341___mcc_h36 = (_source34).name;
        let _342___mcc_h37 = (_source34).opcode;
        let _343___mcc_h38 = (_source34).minCapacity;
        let _344___mcc_h39 = (_source34).minOperands;
        let _345___mcc_h40 = (_source34).pushes;
        let _346___mcc_h41 = (_source34).pops;
        let _347_pops = _346___mcc_h41;
        let _348_pushes = _345___mcc_h40;
        if ((_348_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(2)));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Storage operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right(pos_k);
          }
        }
      } else if (_source34.is_JumpOp) {
        let _349___mcc_h42 = (_source34).name;
        let _350___mcc_h43 = (_source34).opcode;
        let _351___mcc_h44 = (_source34).minCapacity;
        let _352___mcc_h45 = (_source34).minOperands;
        let _353___mcc_h46 = (_source34).pushes;
        let _354___mcc_h47 = (_source34).pops;
        let _355_opcode = _350___mcc_h43;
        if ((_355_opcode) === (EVMConstants.__default.JUMPDEST)) {
          return MiscTypes.Either.create_Right(pos_k);
        } else if (((EVMConstants.__default.JUMP) <= (_355_opcode)) && ((_355_opcode) <= (EVMConstants.__default.JUMPI))) {
          let _356_k = ((_355_opcode) - (EVMConstants.__default.JUMP)) + (1);
          return MiscTypes.Either.create_Right((pos_k).plus(new BigNumber(_356_k)));
        } else {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("Not implemented")));
        }
      } else if (_source34.is_RunOp) {
        let _357___mcc_h48 = (_source34).name;
        let _358___mcc_h49 = (_source34).opcode;
        let _359___mcc_h50 = (_source34).minCapacity;
        let _360___mcc_h51 = (_source34).minOperands;
        let _361___mcc_h52 = (_source34).pushes;
        let _362___mcc_h53 = (_source34).pops;
        let _363_pops = _362___mcc_h53;
        let _364_pushes = _361___mcc_h52;
        if ((pos_k).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Run operator with target 0")));
        } else {
          return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
        }
      } else if (_source34.is_StackOp) {
        let _365___mcc_h54 = (_source34).name;
        let _366___mcc_h55 = (_source34).opcode;
        let _367___mcc_h56 = (_source34).minCapacity;
        let _368___mcc_h57 = (_source34).minOperands;
        let _369___mcc_h58 = (_source34).pushes;
        let _370___mcc_h59 = (_source34).pops;
        let _371_opcode = _366___mcc_h55;
        if (((EVMConstants.__default.PUSH0) <= (_371_opcode)) && ((_371_opcode) <= (EVMConstants.__default.PUSH32))) {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Value(Instructions.__default.GetArgValuePush((_this).dtor_arg)));
          } else {
            return MiscTypes.Either.create_Right((pos_k).minus(_dafny.ONE));
          }
        } else if (((EVMConstants.__default.DUP1) <= (_371_opcode)) && ((_371_opcode) <= (EVMConstants.__default.DUP16))) {
          return MiscTypes.Either.create_Right((((pos_k).isEqualTo(_dafny.ZERO)) ? (new BigNumber((_371_opcode) - (EVMConstants.__default.DUP1))) : ((pos_k).minus(_dafny.ONE))));
        } else if (((EVMConstants.__default.SWAP1) <= (_371_opcode)) && ((_371_opcode) <= (EVMConstants.__default.SWAP16))) {
          let _372_k = (new BigNumber((_371_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE);
          return MiscTypes.Either.create_Right((((pos_k).isEqualTo(_dafny.ZERO)) ? (_372_k) : ((((pos_k).isEqualTo(_372_k)) ? (_dafny.ZERO) : (pos_k)))));
        } else {
          return MiscTypes.Either.create_Right((pos_k).plus(_dafny.ONE));
        }
      } else if (_source34.is_LogOp) {
        let _373___mcc_h60 = (_source34).name;
        let _374___mcc_h61 = (_source34).opcode;
        let _375___mcc_h62 = (_source34).minCapacity;
        let _376___mcc_h63 = (_source34).minOperands;
        let _377___mcc_h64 = (_source34).pushes;
        let _378___mcc_h65 = (_source34).pops;
        let _379_pops = _378___mcc_h65;
        let _380_pushes = _377___mcc_h64;
        return MiscTypes.Either.create_Right((pos_k).plus(_379_pops));
      } else {
        let _381___mcc_h66 = (_source34).name;
        let _382___mcc_h67 = (_source34).opcode;
        let _383___mcc_h68 = (_source34).minCapacity;
        let _384___mcc_h69 = (_source34).minOperands;
        let _385___mcc_h70 = (_source34).pushes;
        let _386___mcc_h71 = (_source34).pops;
        let _387_pops = _386___mcc_h71;
        let _388_pushes = _385___mcc_h70;
        if ((_388_pushes).isEqualTo(_dafny.ZERO)) {
          return MiscTypes.Either.create_Right((pos_k).plus(_387_pops));
        } else {
          if ((pos_k).isEqualTo(_dafny.ZERO)) {
            return MiscTypes.Either.create_Left(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("More than one predecessor. Sys operator with target 0")));
          } else {
            return MiscTypes.Either.create_Right((pos_k).plus(_387_pops));
          }
        }
      }
    };
    NextState(s, jumpDests, exit) {
      let _this = this;
      let _source35 = (_this).dtor_op;
      if (_source35.is_ArithOp) {
        let _389___mcc_h0 = (_source35).name;
        let _390___mcc_h1 = (_source35).opcode;
        let _391___mcc_h2 = (_source35).minCapacity;
        let _392___mcc_h3 = (_source35).minOperands;
        let _393___mcc_h4 = (_source35).pushes;
        let _394___mcc_h5 = (_source35).pops;
        let _395_pops = _394___mcc_h5;
        let _396_pushes = _393___mcc_h4;
        if ((_395_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_395_pops)).PushNRandom(_396_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source35.is_CompOp) {
        let _397___mcc_h6 = (_source35).name;
        let _398___mcc_h7 = (_source35).opcode;
        let _399___mcc_h8 = (_source35).minCapacity;
        let _400___mcc_h9 = (_source35).minOperands;
        let _401___mcc_h10 = (_source35).pushes;
        let _402___mcc_h11 = (_source35).pops;
        let _403_pops = _402___mcc_h11;
        let _404_pushes = _401___mcc_h10;
        if ((_403_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_403_pops)).PushNRandom(_404_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source35.is_BitwiseOp) {
        let _405___mcc_h12 = (_source35).name;
        let _406___mcc_h13 = (_source35).opcode;
        let _407___mcc_h14 = (_source35).minCapacity;
        let _408___mcc_h15 = (_source35).minOperands;
        let _409___mcc_h16 = (_source35).pushes;
        let _410___mcc_h17 = (_source35).pops;
        let _411_pops = _410___mcc_h17;
        let _412_pushes = _409___mcc_h16;
        if ((_411_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_411_pops)).PushNRandom(_412_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source35.is_KeccakOp) {
        let _413___mcc_h18 = (_source35).name;
        let _414___mcc_h19 = (_source35).opcode;
        let _415___mcc_h20 = (_source35).minCapacity;
        let _416___mcc_h21 = (_source35).minOperands;
        let _417___mcc_h22 = (_source35).pushes;
        let _418___mcc_h23 = (_source35).pops;
        let _419_pops = _418___mcc_h23;
        let _420_pushes = _417___mcc_h22;
        if ((new BigNumber(2)).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(new BigNumber(2))).Push(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("")))).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack underflow"));
        }
      } else if (_source35.is_EnvOp) {
        let _421___mcc_h24 = (_source35).name;
        let _422___mcc_h25 = (_source35).opcode;
        let _423___mcc_h26 = (_source35).minCapacity;
        let _424___mcc_h27 = (_source35).minOperands;
        let _425___mcc_h28 = (_source35).pushes;
        let _426___mcc_h29 = (_source35).pops;
        let _427_pops = _426___mcc_h29;
        let _428_pushes = _425___mcc_h28;
        if ((_427_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_427_pops)).PushNRandom(_428_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("EnvOp error"));
        }
      } else if (_source35.is_MemOp) {
        let _429___mcc_h30 = (_source35).name;
        let _430___mcc_h31 = (_source35).opcode;
        let _431___mcc_h32 = (_source35).minCapacity;
        let _432___mcc_h33 = (_source35).minOperands;
        let _433___mcc_h34 = (_source35).pushes;
        let _434___mcc_h35 = (_source35).pops;
        let _435_pops = _434___mcc_h35;
        let _436_pushes = _433___mcc_h34;
        if ((_435_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_435_pops)).PushNRandom(_436_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("MemOp error"));
        }
      } else if (_source35.is_StorageOp) {
        let _437___mcc_h36 = (_source35).name;
        let _438___mcc_h37 = (_source35).opcode;
        let _439___mcc_h38 = (_source35).minCapacity;
        let _440___mcc_h39 = (_source35).minOperands;
        let _441___mcc_h40 = (_source35).pushes;
        let _442___mcc_h41 = (_source35).pops;
        let _443_pops = _442___mcc_h41;
        let _444_pushes = _441___mcc_h40;
        if ((_443_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_443_pops)).PushNRandom(_444_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Storage Op error"));
        }
      } else if (_source35.is_JumpOp) {
        let _445___mcc_h42 = (_source35).name;
        let _446___mcc_h43 = (_source35).opcode;
        let _447___mcc_h44 = (_source35).minCapacity;
        let _448___mcc_h45 = (_source35).minOperands;
        let _449___mcc_h46 = (_source35).pushes;
        let _450___mcc_h47 = (_source35).pops;
        let _451_pops = _450___mcc_h47;
        let _452_pushes = _449___mcc_h46;
        let _453_opcode = _446___mcc_h43;
        if ((_453_opcode) === (EVMConstants.__default.JUMPDEST)) {
          return (s).Skip(_dafny.ONE);
        } else if ((_453_opcode) === (EVMConstants.__default.JUMP)) {
          if ((_dafny.ONE).isLessThanOrEqualTo((s).Size())) {
            let _source36 = (s).Peek(_dafny.ZERO);
            if (_source36.is_Value) {
              let _454___mcc_h72 = (_source36).v;
              let _455_v = _454___mcc_h72;
              return ((s).Pop()).Goto(_455_v);
            } else {
              let _456___mcc_h73 = (_source36).s;
              return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Jump to Random() unknown PC error"));
            }
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Cannot execute JUMP/exit false or stack underflow"));
          }
        } else if ((_453_opcode) === (EVMConstants.__default.JUMPI)) {
          if ((new BigNumber(2)).isLessThanOrEqualTo((s).Size())) {
            let _source37 = (s).Peek(_dafny.ZERO);
            if (_source37.is_Value) {
              let _457___mcc_h74 = (_source37).v;
              let _458_v = _457___mcc_h74;
              if ((_dafny.ONE).isLessThanOrEqualTo(exit)) {
                return ((s).PopN(new BigNumber(2))).Goto(_458_v);
              } else {
                return ((s).PopN(new BigNumber(2))).Skip(_dafny.ONE);
              }
            } else {
              let _459___mcc_h75 = (_source37).s;
              return State.AState.create_Error(_dafny.Seq.UnicodeFromString("JumpI to Random() error"));
            }
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Cannot execute JUMPI/strack underflow"));
          }
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("RJUMPs not implemented"));
        }
      } else if (_source35.is_RunOp) {
        let _460___mcc_h48 = (_source35).name;
        let _461___mcc_h49 = (_source35).opcode;
        let _462___mcc_h50 = (_source35).minCapacity;
        let _463___mcc_h51 = (_source35).minOperands;
        let _464___mcc_h52 = (_source35).pushes;
        let _465___mcc_h53 = (_source35).pops;
        let _466_pops = _465___mcc_h53;
        let _467_pushes = _464___mcc_h52;
        return ((s).Push(StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString("")))).Skip(_dafny.ONE);
      } else if (_source35.is_StackOp) {
        let _468___mcc_h54 = (_source35).name;
        let _469___mcc_h55 = (_source35).opcode;
        let _470___mcc_h56 = (_source35).minCapacity;
        let _471___mcc_h57 = (_source35).minOperands;
        let _472___mcc_h58 = (_source35).pushes;
        let _473___mcc_h59 = (_source35).pops;
        let _474_pops = _473___mcc_h59;
        let _475_pushes = _472___mcc_h58;
        let _476_opcode = _469___mcc_h55;
        if (((_476_opcode) === (EVMConstants.__default.POP)) && ((_dafny.ONE).isLessThanOrEqualTo((s).Size()))) {
          return ((s).Pop()).Skip(_dafny.ONE);
        } else if (((EVMConstants.__default.PUSH0) <= (_476_opcode)) && ((_476_opcode) <= (EVMConstants.__default.PUSH32))) {
          let _477_valToPush = ((_dafny.Seq.contains(jumpDests, Instructions.__default.GetArgValuePush((_this).dtor_arg))) ? (StackElement.StackElem.create_Value(Instructions.__default.GetArgValuePush((_this).dtor_arg))) : (StackElement.StackElem.create_Random(_dafny.Seq.UnicodeFromString(""))));
          return ((s).Push(_477_valToPush)).Skip((_dafny.ONE).plus(new BigNumber((_476_opcode) - (EVMConstants.__default.PUSH0))));
        } else if ((((EVMConstants.__default.DUP1) <= (_476_opcode)) && ((_476_opcode) <= (EVMConstants.__default.DUP16))) && (((new BigNumber((_476_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE)).isLessThanOrEqualTo((s).Size()))) {
          return ((s).Dup((new BigNumber((_476_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE))).Skip(_dafny.ONE);
        } else if ((((EVMConstants.__default.SWAP1) <= (_476_opcode)) && ((_476_opcode) <= (EVMConstants.__default.SWAP16))) && (((new BigNumber((_476_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE)).isLessThan((s).Size()))) {
          return ((s).Swap((new BigNumber((_476_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE))).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Stack Op error"));
        }
      } else if (_source35.is_LogOp) {
        let _478___mcc_h60 = (_source35).name;
        let _479___mcc_h61 = (_source35).opcode;
        let _480___mcc_h62 = (_source35).minCapacity;
        let _481___mcc_h63 = (_source35).minOperands;
        let _482___mcc_h64 = (_source35).pushes;
        let _483___mcc_h65 = (_source35).pops;
        let _484_pops = _483___mcc_h65;
        let _485_pushes = _482___mcc_h64;
        if ((_484_pops).isLessThanOrEqualTo((s).Size())) {
          return ((s).PopN(_484_pops)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("LogOp error"));
        }
      } else {
        let _486___mcc_h66 = (_source35).name;
        let _487___mcc_h67 = (_source35).opcode;
        let _488___mcc_h68 = (_source35).minCapacity;
        let _489___mcc_h69 = (_source35).minOperands;
        let _490___mcc_h70 = (_source35).pushes;
        let _491___mcc_h71 = (_source35).pops;
        let _492_pops = _491___mcc_h71;
        let _493_pushes = _490___mcc_h70;
        let _494_op = _487___mcc_h67;
        if ((((_494_op) === (EVMConstants.__default.INVALID)) || ((_494_op) === (EVMConstants.__default.STOP))) || ((_494_op) === (EVMConstants.__default.REVERT))) {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("SysOp error"));
        } else if ((_492_pops).isLessThanOrEqualTo((s).Size())) {
          return (((s).PopN(_492_pops)).PushNRandom(_493_pushes)).Skip(_dafny.ONE);
        } else {
          return State.AState.create_Error(_dafny.Seq.UnicodeFromString("SysOp error"));
        }
      }
    };
    WPre(c) {
      let _this = this;
      let _source38 = (_this).dtor_op;
      if (_source38.is_ArithOp) {
        let _495___mcc_h0 = (_source38).name;
        let _496___mcc_h1 = (_source38).opcode;
        let _497___mcc_h2 = (_source38).minCapacity;
        let _498___mcc_h3 = (_source38).minOperands;
        let _499___mcc_h4 = (_source38).pushes;
        let _500___mcc_h5 = (_source38).pops;
        let _501_pops = _500___mcc_h5;
        let _502_pushes = _499___mcc_h4;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _503_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_504_pos) {
            return (_504_pos).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_503_shiftByOne, (c).TrackedVals());
        }
      } else if (_source38.is_CompOp) {
        let _505___mcc_h6 = (_source38).name;
        let _506___mcc_h7 = (_source38).opcode;
        let _507___mcc_h8 = (_source38).minCapacity;
        let _508___mcc_h9 = (_source38).minOperands;
        let _509___mcc_h10 = (_source38).pushes;
        let _510___mcc_h11 = (_source38).pops;
        let _511_pops = _510___mcc_h11;
        let _512_pushes = _509___mcc_h10;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _513_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_514_pops, _515_pushes) => function (_516_pos) {
            return ((_516_pos).plus(_514_pops)).minus(_515_pushes);
          })(_511_pops, _512_pushes));
          return WeakPre.Cond.create_StCond(_513_shiftBy, (c).TrackedVals());
        }
      } else if (_source38.is_BitwiseOp) {
        let _517___mcc_h12 = (_source38).name;
        let _518___mcc_h13 = (_source38).opcode;
        let _519___mcc_h14 = (_source38).minCapacity;
        let _520___mcc_h15 = (_source38).minOperands;
        let _521___mcc_h16 = (_source38).pushes;
        let _522___mcc_h17 = (_source38).pops;
        let _523_pops = _522___mcc_h17;
        let _524_pushes = _521___mcc_h16;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _525_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_526_pops, _527_pushes) => function (_528_pos) {
            return ((_528_pos).plus(_526_pops)).minus(_527_pushes);
          })(_523_pops, _524_pushes));
          return WeakPre.Cond.create_StCond(_525_shiftBy, (c).TrackedVals());
        }
      } else if (_source38.is_KeccakOp) {
        let _529___mcc_h18 = (_source38).name;
        let _530___mcc_h19 = (_source38).opcode;
        let _531___mcc_h20 = (_source38).minCapacity;
        let _532___mcc_h21 = (_source38).minOperands;
        let _533___mcc_h22 = (_source38).pushes;
        let _534___mcc_h23 = (_source38).pops;
        let _535_pops = _534___mcc_h23;
        let _536_pushes = _533___mcc_h22;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _537_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_538_pos) {
            return (_538_pos).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_537_shiftByOne, (c).TrackedVals());
        }
      } else if (_source38.is_EnvOp) {
        let _539___mcc_h24 = (_source38).name;
        let _540___mcc_h25 = (_source38).opcode;
        let _541___mcc_h26 = (_source38).minCapacity;
        let _542___mcc_h27 = (_source38).minOperands;
        let _543___mcc_h28 = (_source38).pushes;
        let _544___mcc_h29 = (_source38).pops;
        let _545_pops = _544___mcc_h29;
        let _546_pushes = _543___mcc_h28;
        if (((_546_pushes).isEqualTo(_dafny.ONE)) && ((_545_pops).isEqualTo(_dafny.ZERO))) {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            let _547_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_548_pos) {
              return (_548_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_547_shiftByOne, (c).TrackedVals());
          }
        } else if (((_546_pushes).isEqualTo(_dafny.ONE)) && ((_545_pops).isEqualTo(_dafny.ONE))) {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        } else {
          let _549_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_550_pops, _551_pushes) => function (_552_pos) {
            return ((_552_pos).plus(_550_pops)).minus(_551_pushes);
          })(_545_pops, _546_pushes));
          return WeakPre.Cond.create_StCond(_549_shiftBy, (c).TrackedVals());
        }
      } else if (_source38.is_MemOp) {
        let _553___mcc_h30 = (_source38).name;
        let _554___mcc_h31 = (_source38).opcode;
        let _555___mcc_h32 = (_source38).minCapacity;
        let _556___mcc_h33 = (_source38).minOperands;
        let _557___mcc_h34 = (_source38).pushes;
        let _558___mcc_h35 = (_source38).pops;
        let _559_pops = _558___mcc_h35;
        let _560_pushes = _557___mcc_h34;
        if ((_560_pushes).isEqualTo(_dafny.ZERO)) {
          let _561_shiftByTwo = MiscTypes.__default.Map((c).TrackedPos(), function (_562_pos) {
            return (_562_pos).plus(new BigNumber(2));
          });
          return WeakPre.Cond.create_StCond(_561_shiftByTwo, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        }
      } else if (_source38.is_StorageOp) {
        let _563___mcc_h36 = (_source38).name;
        let _564___mcc_h37 = (_source38).opcode;
        let _565___mcc_h38 = (_source38).minCapacity;
        let _566___mcc_h39 = (_source38).minOperands;
        let _567___mcc_h40 = (_source38).pushes;
        let _568___mcc_h41 = (_source38).pops;
        let _569_pops = _568___mcc_h41;
        let _570_pushes = _567___mcc_h40;
        if ((_570_pushes).isEqualTo(_dafny.ZERO)) {
          let _571_shiftByTwo = MiscTypes.__default.Map((c).TrackedPos(), function (_572_pos) {
            return (_572_pos).plus(new BigNumber(2));
          });
          return WeakPre.Cond.create_StCond(_571_shiftByTwo, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            return c;
          }
        }
      } else if (_source38.is_JumpOp) {
        let _573___mcc_h42 = (_source38).name;
        let _574___mcc_h43 = (_source38).opcode;
        let _575___mcc_h44 = (_source38).minCapacity;
        let _576___mcc_h45 = (_source38).minOperands;
        let _577___mcc_h46 = (_source38).pushes;
        let _578___mcc_h47 = (_source38).pops;
        let _579_opcode = _574___mcc_h43;
        if ((_579_opcode) === (EVMConstants.__default.JUMPDEST)) {
          return c;
        } else if (((EVMConstants.__default.JUMP) <= (_579_opcode)) && ((_579_opcode) <= (EVMConstants.__default.JUMPI))) {
          let _580_k = ((_579_opcode) - (EVMConstants.__default.JUMP)) + (1);
          let _581_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_582_k) => function (_583_pos) {
            return (_583_pos).plus(new BigNumber(_582_k));
          })(_580_k));
          return WeakPre.Cond.create_StCond(_581_shiftBy, (c).TrackedVals());
        } else {
          return WeakPre.Cond.create_StFalse();
        }
      } else if (_source38.is_RunOp) {
        let _584___mcc_h48 = (_source38).name;
        let _585___mcc_h49 = (_source38).opcode;
        let _586___mcc_h50 = (_source38).minCapacity;
        let _587___mcc_h51 = (_source38).minOperands;
        let _588___mcc_h52 = (_source38).pushes;
        let _589___mcc_h53 = (_source38).pops;
        let _590_opcode = _585___mcc_h49;
        if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
          return WeakPre.Cond.create_StFalse();
        } else {
          let _591_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_592_pos) {
            return (_592_pos).minus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_591_shiftByOne, (c).TrackedVals());
        }
      } else if (_source38.is_StackOp) {
        let _593___mcc_h54 = (_source38).name;
        let _594___mcc_h55 = (_source38).opcode;
        let _595___mcc_h56 = (_source38).minCapacity;
        let _596___mcc_h57 = (_source38).minOperands;
        let _597___mcc_h58 = (_source38).pushes;
        let _598___mcc_h59 = (_source38).pops;
        let _599_opcode = _594___mcc_h55;
        if (((EVMConstants.__default.PUSH0) <= (_599_opcode)) && ((_599_opcode) <= (EVMConstants.__default.PUSH32))) {
          let _source39 = MiscTypes.__default.Find((c).TrackedPos(), _dafny.ZERO);
          if (_source39.is_None) {
            let _600_shiftByMinusOne = MiscTypes.__default.Map((c).TrackedPos(), function (_601_pos) {
              return (_601_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_600_shiftByMinusOne, (c).TrackedVals());
          } else {
            let _602___mcc_h72 = (_source39).v;
            let _603_i = _602___mcc_h72;
            let _604_argVal = Hex.__default.HexToU256(_dafny.Seq.Concat(_dafny.Seq.Create((new BigNumber(64)).minus(new BigNumber(((_this).dtor_arg).length)), function (_605___v142) {
              return new _dafny.CodePoint('0'.codePointAt(0));
            }), (_this).dtor_arg));
            if (_dafny.areEqual((c).TrackedValAt(_603_i), (_604_argVal).Extract())) {
              let _606_filtered = _dafny.Seq.Concat(((c).TrackedPos()).slice(0, _603_i), ((c).TrackedPos()).slice((_603_i).plus(_dafny.ONE)));
              if ((new BigNumber((_606_filtered).length)).isEqualTo(_dafny.ZERO)) {
                return WeakPre.Cond.create_StTrue();
              } else {
                let _607_shiftByMinusOne = MiscTypes.__default.Map(_606_filtered, function (_608_pos) {
                  return (_608_pos).minus(_dafny.ONE);
                });
                return WeakPre.Cond.create_StCond(_607_shiftByMinusOne, _dafny.Seq.Concat(((c).TrackedVals()).slice(0, _603_i), ((c).TrackedVals()).slice((_603_i).plus(_dafny.ONE))));
              }
            } else {
              return WeakPre.Cond.create_StFalse();
            }
          }
        } else if (((EVMConstants.__default.DUP1) <= (_599_opcode)) && ((_599_opcode) <= (EVMConstants.__default.DUP16))) {
          let _source40 = MiscTypes.__default.Find((c).TrackedPos(), _dafny.ZERO);
          if (_source40.is_None) {
            let _609_shiftByMinusOneButZero = MiscTypes.__default.Map((c).TrackedPos(), function (_610_pos) {
              return (_610_pos).minus(_dafny.ONE);
            });
            return WeakPre.Cond.create_StCond(_609_shiftByMinusOneButZero, (c).TrackedVals());
          } else {
            let _611___mcc_h73 = (_source40).v;
            let _612_index0 = _611___mcc_h73;
            let _source41 = MiscTypes.__default.Find((c).TrackedPos(), (new BigNumber((_599_opcode) - (EVMConstants.__default.DUP1))).plus(_dafny.ONE));
            if (_source41.is_None) {
              let _613_shiftByMinusOneButZero = MiscTypes.__default.Map((c).TrackedPos(), ((_614_opcode) => function (_615_pos) {
                return (((_615_pos).isEqualTo(_dafny.ZERO)) ? (new BigNumber((_614_opcode) - (EVMConstants.__default.DUP1))) : ((_615_pos).minus(_dafny.ONE)));
              })(_599_opcode));
              return WeakPre.Cond.create_StCond(_613_shiftByMinusOneButZero, (c).TrackedVals());
            } else {
              let _616___mcc_h74 = (_source41).v;
              let _617_index = _616___mcc_h74;
              if (_dafny.areEqual((c).TrackedValAt(_612_index0), (c).TrackedValAt(_617_index))) {
                let _618_filtered = _dafny.Seq.Concat(((c).TrackedPos()).slice(0, _612_index0), ((c).TrackedPos()).slice((_612_index0).plus(_dafny.ONE)));
                let _619_shiftByMinusOne = MiscTypes.__default.Map(_618_filtered, function (_620_pos) {
                  return (_620_pos).minus(_dafny.ONE);
                });
                return WeakPre.Cond.create_StCond(_619_shiftByMinusOne, _dafny.Seq.Concat(((c).TrackedVals()).slice(0, _612_index0), ((c).TrackedVals()).slice((_612_index0).plus(_dafny.ONE))));
              } else {
                return WeakPre.Cond.create_StFalse();
              }
            }
          }
        } else if (((EVMConstants.__default.SWAP1) <= (_599_opcode)) && ((_599_opcode) <= (EVMConstants.__default.SWAP16))) {
          let _621_k = (new BigNumber((_599_opcode) - (EVMConstants.__default.SWAP1))).plus(_dafny.ONE);
          let _622_swapZeroAndk = MiscTypes.__default.Map((c).TrackedPos(), ((_623_k) => function (_624_pos) {
            return (((_624_pos).isEqualTo(_dafny.ZERO)) ? ((_623_k)) : ((((_624_pos).isEqualTo(_623_k)) ? (_dafny.ZERO) : (_624_pos))));
          })(_621_k));
          return WeakPre.Cond.create_StCond(_622_swapZeroAndk, (c).TrackedVals());
        } else {
          let _625_shiftByOne = MiscTypes.__default.Map((c).TrackedPos(), function (_626_i) {
            return (_626_i).plus(_dafny.ONE);
          });
          return WeakPre.Cond.create_StCond(_625_shiftByOne, (c).TrackedVals());
        }
      } else if (_source38.is_LogOp) {
        let _627___mcc_h60 = (_source38).name;
        let _628___mcc_h61 = (_source38).opcode;
        let _629___mcc_h62 = (_source38).minCapacity;
        let _630___mcc_h63 = (_source38).minOperands;
        let _631___mcc_h64 = (_source38).pushes;
        let _632___mcc_h65 = (_source38).pops;
        let _633_pops = _632___mcc_h65;
        let _634_pushes = _631___mcc_h64;
        let _635_opcode = _628___mcc_h61;
        let _636_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_637_pops) => function (_638_pos) {
          return (_638_pos).plus(_637_pops);
        })(_633_pops));
        return WeakPre.Cond.create_StCond(_636_shiftBy, (c).TrackedVals());
      } else {
        let _639___mcc_h66 = (_source38).name;
        let _640___mcc_h67 = (_source38).opcode;
        let _641___mcc_h68 = (_source38).minCapacity;
        let _642___mcc_h69 = (_source38).minOperands;
        let _643___mcc_h70 = (_source38).pushes;
        let _644___mcc_h71 = (_source38).pops;
        let _645_pops = _644___mcc_h71;
        let _646_pushes = _643___mcc_h70;
        let _647_opcode = _640___mcc_h67;
        if ((_646_pushes).isEqualTo(_dafny.ZERO)) {
          let _648_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_649_pops) => function (_650_pos) {
            return (_650_pos).plus(_649_pops);
          })(_645_pops));
          return WeakPre.Cond.create_StCond(_648_shiftBy, (c).TrackedVals());
        } else {
          if (_dafny.Seq.contains((c).TrackedPos(), _dafny.ZERO)) {
            return WeakPre.Cond.create_StFalse();
          } else {
            let _651_shiftBy = MiscTypes.__default.Map((c).TrackedPos(), ((_652_pops) => function (_653_pos) {
              return (_653_pos).plus(_652_pops);
            })(_645_pops));
            return WeakPre.Cond.create_StCond(_651_shiftBy, (c).TrackedVals());
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
          return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Odd number of characters ending in "), s), next)));
        } else {
          let _source42 = Hex.__default.HexToU8((s).slice(0, new BigNumber(2)));
          if (_source42.is_None) {
            return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("'"), (s).slice(0, new BigNumber(2))), _dafny.Seq.UnicodeFromString("' is not an Hex number")), next)));
          } else {
            let _654___mcc_h0 = (_source42).v;
            let _655_v = _654___mcc_h0;
            let _656_op = OpcodeDecoder.__default.Decode(_655_v);
            if ((_dafny.ZERO).isLessThan((_656_op).Args())) {
              if (((new BigNumber(((s).slice(new BigNumber(2))).length)).isLessThan((new BigNumber(2)).multipliedBy((_656_op).Args()))) || (!(Hex.__default.IsHexString(((s).slice(new BigNumber(2))).slice(0, (new BigNumber(2)).multipliedBy((_656_op).Args())))))) {
                return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("not enough arguments for opcode "), (_656_op).dtor_name), next)));
              } else {
                let _in29 = ((s).slice(new BigNumber(2))).slice((new BigNumber(2)).multipliedBy((_656_op).Args()));
                let _in30 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_656_op, ((s).slice(new BigNumber(2))).slice(0, (new BigNumber(2)).multipliedBy((_656_op).Args())), next)));
                let _in31 = ((next).plus(_dafny.ONE)).plus((_656_op).Args());
                s = _in29;
                p = _in30;
                next = _in31;
                continue TAIL_CALL_START;
              }
            } else {
              let _in32 = (s).slice(new BigNumber(2));
              let _in33 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_656_op, _dafny.Seq.of(), next)));
              let _in34 = (next).plus(_dafny.ONE);
              s = _in32;
              p = _in33;
              next = _in34;
              continue TAIL_CALL_START;
            }
          }
        }
      }
    };
    static DisassembleU8(s, p, next) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return p;
        } else {
          let _657_op = OpcodeDecoder.__default.Decode((s)[_dafny.ZERO]);
          if ((_dafny.ZERO).isLessThan((_657_op).Args())) {
            if ((new BigNumber(((s).slice(_dafny.ONE)).length)).isLessThan((_657_op).Args())) {
              return _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(OpcodeDecoder.__default.Decode(EVMConstants.__default.INVALID), _dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("not enough arguments for opcode "), (_657_op).dtor_name), next)));
            } else {
              let _in35 = ((s).slice(_dafny.ONE)).slice((_657_op).Args());
              let _in36 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_657_op, Hex.__default.HexHelper(((s).slice(_dafny.ONE)).slice(0, (_657_op).Args())), next)));
              let _in37 = ((next).plus(_dafny.ONE)).plus((_657_op).Args());
              s = _in35;
              p = _in36;
              next = _in37;
              continue TAIL_CALL_START;
            }
          } else {
            let _in38 = (s).slice(_dafny.ONE);
            let _in39 = _dafny.Seq.Concat(p, _dafny.Seq.of(Instructions.Instruction.create_Instruction(_657_op, _dafny.Seq.of(), next)));
            let _in40 = (next).plus(_dafny.ONE);
            s = _in38;
            p = _in39;
            next = _in40;
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
      let _658___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_658___accumulator);
        } else {
          _658___accumulator = (_658___accumulator).plus(((xs)[_dafny.ZERO]).StackEffect());
          let _in41 = (xs).slice(_dafny.ONE);
          xs = _in41;
          continue TAIL_CALL_START;
        }
      }
    };
    static WeakestPreOperandsHelper(xs, postCond) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return postCond;
        } else {
          let _659_lastI = (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
          let _660_e = (_659_lastI).WeakestPreOperands(postCond);
          let _in42 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in43 = _660_e;
          xs = _in42;
          postCond = _in43;
          continue TAIL_CALL_START;
        }
      }
    };
    static WeakestPreCapacityHelper(xs, postCond) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return postCond;
        } else {
          let _661_lastI = (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
          let _662_e = (_661_lastI).WeakestPreCapacity(postCond);
          let _in44 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in45 = _662_e;
          xs = _in44;
          postCond = _in45;
          continue TAIL_CALL_START;
        }
      }
    };
    static RunIns(xs, s, jumpDests) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return s;
        } else {
          let _663_next = ((xs)[_dafny.ZERO]).NextState(s, jumpDests, _dafny.ZERO);
          let _source43 = _663_next;
          if (_source43.is_EState) {
            let _664___mcc_h0 = (_source43).pc;
            let _665___mcc_h1 = (_source43).stack;
            let _in46 = (xs).slice(_dafny.ONE);
            let _in47 = _663_next;
            let _in48 = jumpDests;
            xs = _in46;
            s = _in47;
            jumpDests = _in48;
            continue TAIL_CALL_START;
          } else {
            let _666___mcc_h2 = (_source43).msg;
            return _663_next;
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
          let _667_c1 = ((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]).WPre(c);
          let _in49 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
          let _in50 = _667_c1;
          xs = _in49;
          c = _in50;
          continue TAIL_CALL_START;
        }
      }
    };
    static WPreSeqSegs(path, exits, c, xs, tgtPC) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((path).length)).isEqualTo(_dafny.ZERO)) {
          return c;
        } else {
          let _668_w1 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).WPre(c);
          let _669_wp2 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).LeadsTo(tgtPC, (exits)[(new BigNumber((exits).length)).minus(_dafny.ONE)]);
          let _in51 = (path).slice(0, (new BigNumber((path).length)).minus(_dafny.ONE));
          let _in52 = (exits).slice(0, (new BigNumber((exits).length)).minus(_dafny.ONE));
          let _in53 = (_668_w1).And(_669_wp2);
          let _in54 = xs;
          let _in55 = ((xs)[(path)[(new BigNumber((path).length)).minus(_dafny.ONE)]]).StartAddress();
          path = _in51;
          exits = _in52;
          c = _in53;
          xs = _in54;
          tgtPC = _in55;
          continue TAIL_CALL_START;
        }
      }
    };
    static EquivSeg(s1, s2) {
      let _source44 = s1;
      if (_source44.is_JUMPSeg) {
        let _670___mcc_h0 = (_source44).ins;
        let _671___mcc_h1 = (_source44).lastIns;
        let _672___mcc_h2 = (_source44).netOpEffect;
        return ((((s2).is_JUMPSeg) && (((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length))) && ((new BigNumber(2)).isLessThanOrEqualTo(new BigNumber(((s2).Ins()).length))))) && ((((EVMConstants.__default.PUSH1) <= (((((s1).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode)) && ((((((s1).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode) === (((((s2).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode))) && ((((((s2).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode) <= (EVMConstants.__default.PUSH32)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, (new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)), true, function (_forall_var_3) {
          let _673_i = _forall_var_3;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_673_i)) && ((_673_i).isLessThan((new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)))) || ((((s1).dtor_ins)[_673_i]).Equiv(((s2).dtor_ins)[_673_i]));
        }));
      } else if (_source44.is_JUMPISeg) {
        let _674___mcc_h3 = (_source44).ins;
        let _675___mcc_h4 = (_source44).lastIns;
        let _676___mcc_h5 = (_source44).netOpEffect;
        return ((((s2).is_JUMPISeg) && (((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length))) && ((new BigNumber(2)).isLessThanOrEqualTo(new BigNumber(((s2).Ins()).length))))) && ((((EVMConstants.__default.PUSH1) <= (((((s1).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode)) && ((((((s1).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode) === (((((s2).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode))) && ((((((s2).dtor_ins)[(new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)]).dtor_op).dtor_opcode) <= (EVMConstants.__default.PUSH32)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, (new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)), true, function (_forall_var_4) {
          let _677_i = _forall_var_4;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_677_i)) && ((_677_i).isLessThan((new BigNumber(((s1).dtor_ins).length)).minus(_dafny.ONE)))) || ((((s1).dtor_ins)[_677_i]).Equiv(((s2).dtor_ins)[_677_i]));
        }));
      } else if (_source44.is_RETURNSeg) {
        let _678___mcc_h6 = (_source44).ins;
        let _679___mcc_h7 = (_source44).lastIns;
        let _680___mcc_h8 = (_source44).netOpEffect;
        return (((s2).is_RETURNSeg) && ((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((s1).Ins()).length)), true, function (_forall_var_5) {
          let _681_i = _forall_var_5;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_681_i)) && ((_681_i).isLessThan(new BigNumber(((s1).Ins()).length)))) || ((((s1).Ins())[_681_i]).Equiv(((s2).Ins())[_681_i]));
        }));
      } else if (_source44.is_STOPSeg) {
        let _682___mcc_h9 = (_source44).ins;
        let _683___mcc_h10 = (_source44).lastIns;
        let _684___mcc_h11 = (_source44).netOpEffect;
        return (((s2).is_STOPSeg) && ((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((s1).Ins()).length)), true, function (_forall_var_6) {
          let _685_i = _forall_var_6;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_685_i)) && ((_685_i).isLessThan(new BigNumber(((s1).Ins()).length)))) || ((((s1).Ins())[_685_i]).Equiv(((s2).Ins())[_685_i]));
        }));
      } else if (_source44.is_CONTSeg) {
        let _686___mcc_h12 = (_source44).ins;
        let _687___mcc_h13 = (_source44).lastIns;
        let _688___mcc_h14 = (_source44).netOpEffect;
        return (((s2).is_CONTSeg) && ((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((s1).Ins()).length)), true, function (_forall_var_7) {
          let _689_i = _forall_var_7;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_689_i)) && ((_689_i).isLessThan(new BigNumber(((s1).Ins()).length)))) || ((((s1).Ins())[_689_i]).Equiv(((s2).Ins())[_689_i]));
        }));
      } else {
        let _690___mcc_h15 = (_source44).ins;
        let _691___mcc_h16 = (_source44).lastIns;
        let _692___mcc_h17 = (_source44).netOpEffect;
        return (((s2).is_INVALIDSeg) && ((new BigNumber(((s1).Ins()).length)).isEqualTo(new BigNumber(((s2).Ins()).length)))) && (_dafny.Quantifier(_dafny.IntegerRange(_dafny.ZERO, new BigNumber(((s1).Ins()).length)), true, function (_forall_var_8) {
          let _693_i = _forall_var_8;
          return !(((_dafny.ZERO).isLessThanOrEqualTo(_693_i)) && ((_693_i).isLessThan(new BigNumber(((s1).Ins()).length)))) || ((((s1).Ins())[_693_i]).Equiv(((s2).Ins())[_693_i]));
        }));
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
    Ins() {
      let _this = this;
      return _dafny.Seq.Concat((_this).dtor_ins, _dafny.Seq.of((_this).dtor_lastIns));
    };
    Size(xi) {
      let _this = this;
      let _694___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xi).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_694___accumulator);
        } else {
          _694___accumulator = (_694___accumulator).plus(((xi)[_dafny.ZERO]).Size());
          let _in56 = _this;
          let _in57 = (xi).slice(_dafny.ONE);
          _this = _in56;
          ;
          xi = _in57;
          continue TAIL_CALL_START;
        }
      }
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
    CollectJumpDest() {
      let _this = this;
      if ((((((_this).Ins())[_dafny.ZERO]).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPDEST)) {
        return _dafny.Seq.of((((_this).Ins())[_dafny.ZERO]).dtor_address);
      } else {
        return _dafny.Seq.of();
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
    Run(s, exit, jumpDests) {
      let _this = this;
      let _695_s_k = LinSegments.__default.RunIns((_this).dtor_ins, s, jumpDests);
      if ((_695_s_k).is_Error) {
        return _695_s_k;
      } else {
        return ((_this).dtor_lastIns).NextState(_695_s_k, jumpDests, exit);
      }
    };
    WPre(c) {
      let _this = this;
      return LinSegments.__default.WPreIns((_this).Ins(), c);
    };
    NumberOfExits() {
      let _this = this;
      let _source45 = _this;
      if (_source45.is_JUMPSeg) {
        let _696___mcc_h0 = (_source45).ins;
        let _697___mcc_h1 = (_source45).lastIns;
        let _698___mcc_h2 = (_source45).netOpEffect;
        return _dafny.ONE;
      } else if (_source45.is_JUMPISeg) {
        let _699___mcc_h6 = (_source45).ins;
        let _700___mcc_h7 = (_source45).lastIns;
        let _701___mcc_h8 = (_source45).netOpEffect;
        return new BigNumber(2);
      } else if (_source45.is_RETURNSeg) {
        let _702___mcc_h12 = (_source45).ins;
        let _703___mcc_h13 = (_source45).lastIns;
        let _704___mcc_h14 = (_source45).netOpEffect;
        return _dafny.ZERO;
      } else if (_source45.is_STOPSeg) {
        let _705___mcc_h18 = (_source45).ins;
        let _706___mcc_h19 = (_source45).lastIns;
        let _707___mcc_h20 = (_source45).netOpEffect;
        return _dafny.ZERO;
      } else if (_source45.is_CONTSeg) {
        let _708___mcc_h24 = (_source45).ins;
        let _709___mcc_h25 = (_source45).lastIns;
        let _710___mcc_h26 = (_source45).netOpEffect;
        return _dafny.ONE;
      } else {
        let _711___mcc_h30 = (_source45).ins;
        let _712___mcc_h31 = (_source45).lastIns;
        let _713___mcc_h32 = (_source45).netOpEffect;
        return _dafny.ZERO;
      }
    };
    IsJump() {
      let _this = this;
      return ((_this).is_JUMPSeg) || ((_this).is_JUMPISeg);
    };
    LeadsTo(k, exit) {
      let _this = this;
      if ((Int.__default.TWO__256).isLessThanOrEqualTo(k)) {
        return WeakPre.Cond.create_StFalse();
      } else {
        let _source46 = _this;
        if (_source46.is_JUMPSeg) {
          let _714___mcc_h0 = (_source46).ins;
          let _715___mcc_h1 = (_source46).lastIns;
          let _716___mcc_h2 = (_source46).netOpEffect;
          if ((exit).isEqualTo(_dafny.ZERO)) {
            let _717_c = WeakPre.Cond.create_StCond(_dafny.Seq.of(_dafny.ZERO), _dafny.Seq.of(k));
            return LinSegments.__default.WPreIns((_this).dtor_ins, _717_c);
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else if (_source46.is_JUMPISeg) {
          let _718___mcc_h3 = (_source46).ins;
          let _719___mcc_h4 = (_source46).lastIns;
          let _720___mcc_h5 = (_source46).netOpEffect;
          if ((exit).isEqualTo(_dafny.ONE)) {
            let _721_c = WeakPre.Cond.create_StCond(_dafny.Seq.of(_dafny.ZERO), _dafny.Seq.of(k));
            return LinSegments.__default.WPreIns((_this).dtor_ins, _721_c);
          } else if ((k).isEqualTo((_this).StartAddressNextSeg())) {
            return WeakPre.Cond.create_StTrue();
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else if (_source46.is_RETURNSeg) {
          let _722___mcc_h6 = (_source46).ins;
          let _723___mcc_h7 = (_source46).lastIns;
          let _724___mcc_h8 = (_source46).netOpEffect;
          return WeakPre.Cond.create_StTrue();
        } else if (_source46.is_STOPSeg) {
          let _725___mcc_h9 = (_source46).ins;
          let _726___mcc_h10 = (_source46).lastIns;
          let _727___mcc_h11 = (_source46).netOpEffect;
          return WeakPre.Cond.create_StTrue();
        } else if (_source46.is_CONTSeg) {
          let _728___mcc_h12 = (_source46).ins;
          let _729___mcc_h13 = (_source46).lastIns;
          let _730___mcc_h14 = (_source46).netOpEffect;
          if (((exit).isEqualTo(_dafny.ZERO)) && ((k).isEqualTo((_this).StartAddressNextSeg()))) {
            return WeakPre.Cond.create_StTrue();
          } else {
            return WeakPre.Cond.create_StFalse();
          }
        } else {
          let _731___mcc_h15 = (_source46).ins;
          let _732___mcc_h16 = (_source46).lastIns;
          let _733___mcc_h17 = (_source46).netOpEffect;
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
    static SplitUpToTerminal(xs, curseq, collected) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          if ((new BigNumber((curseq).length)).isEqualTo(_dafny.ZERO)) {
            return collected;
          } else {
            let _734_newSeg = Splitter.__default.BuildSeg((curseq).slice(0, (new BigNumber((curseq).length)).minus(_dafny.ONE)), (curseq)[(new BigNumber((curseq).length)).minus(_dafny.ONE)]);
            return _dafny.Seq.Concat(collected, _dafny.Seq.of(_734_newSeg));
          }
        } else if (((((xs)[_dafny.ZERO]).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPDEST)) {
          if ((new BigNumber((curseq).length)).isEqualTo(_dafny.ZERO)) {
            let _in58 = (xs).slice(_dafny.ONE);
            let _in59 = _dafny.Seq.of((xs)[_dafny.ZERO]);
            let _in60 = collected;
            xs = _in58;
            curseq = _in59;
            collected = _in60;
            continue TAIL_CALL_START;
          } else {
            let _735_newSeg = Splitter.__default.BuildSeg((curseq).slice(0, (new BigNumber((curseq).length)).minus(_dafny.ONE)), (curseq)[(new BigNumber((curseq).length)).minus(_dafny.ONE)]);
            let _in61 = (xs).slice(_dafny.ONE);
            let _in62 = _dafny.Seq.of((xs)[_dafny.ZERO]);
            let _in63 = _dafny.Seq.Concat(collected, _dafny.Seq.of(_735_newSeg));
            xs = _in61;
            curseq = _in62;
            collected = _in63;
            continue TAIL_CALL_START;
          }
        } else if (((xs)[_dafny.ZERO]).IsTerminal()) {
          let _736_newSeg = Splitter.__default.BuildSeg(curseq, (xs)[_dafny.ZERO]);
          let _in64 = (xs).slice(_dafny.ONE);
          let _in65 = _dafny.Seq.of();
          let _in66 = _dafny.Seq.Concat(collected, _dafny.Seq.of(_736_newSeg));
          xs = _in64;
          curseq = _in65;
          collected = _in66;
          continue TAIL_CALL_START;
        } else {
          let _in67 = (xs).slice(_dafny.ONE);
          let _in68 = _dafny.Seq.Concat(curseq, _dafny.Seq.of((xs)[_dafny.ZERO]));
          let _in69 = collected;
          xs = _in67;
          curseq = _in68;
          collected = _in69;
          continue TAIL_CALL_START;
        }
      }
    };
    static DeltaOperandsHelper(xs, current) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return current;
        } else {
          let _737_e = (current).plus(((((xs)[_dafny.ZERO]).dtor_op).dtor_pushes).minus((((xs)[_dafny.ZERO]).dtor_op).dtor_pops));
          let _in70 = (xs).slice(_dafny.ONE);
          let _in71 = _737_e;
          xs = _in70;
          current = _in71;
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
          let _738_x = ((xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)]).StackPosBackWardTracker(pos);
          let _source47 = _738_x;
          if (_source47.is_Left) {
            let _739___mcc_h0 = (_source47).l;
            let _740_v = _739___mcc_h0;
            return MiscTypes.Either.create_Left(_740_v);
          } else {
            let _741___mcc_h1 = (_source47).r;
            let _742_v = _741___mcc_h1;
            let _in72 = (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
            let _in73 = _742_v;
            xs = _in72;
            pos = _in73;
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
      let _source48 = _this;
      if (_source48.is_JUMP) {
        let _743___mcc_h0 = (_source48).s;
        let _744___mcc_h1 = (_source48).wpOp;
        let _745___mcc_h2 = (_source48).wpCap;
        let _746___mcc_h3 = (_source48).tgt;
        let _747___mcc_h4 = (_source48).stacks;
        return (((_this).dtor_s).is_JUMPSeg) || (((_this).dtor_s).is_JUMPISeg);
      } else if (_source48.is_CONT) {
        let _748___mcc_h5 = (_source48).s;
        let _749___mcc_h6 = (_source48).wpOp;
        let _750___mcc_h7 = (_source48).wpCap;
        let _751___mcc_h8 = (_source48).stacks;
        return ((_this).dtor_s).is_CONTSeg;
      } else {
        let _752___mcc_h9 = (_source48).s;
        let _753___mcc_h10 = (_source48).wpOp;
        let _754___mcc_h11 = (_source48).wpCap;
        let _755___mcc_h12 = (_source48).stacks;
        return ((((_this).dtor_s).is_RETURNSeg) || (((_this).dtor_s).is_STOPSeg)) || (((_this).dtor_s).is_INVALIDSeg);
      }
    };
    CollectJumpDest() {
      let _this = this;
      return ((_this).dtor_s).CollectJumpDest();
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
      let _756___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((n).isLessThan(new BigNumber(10))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(PrettyIns.__default.DecToChar(n)), _756___accumulator);
        } else {
          _756___accumulator = _dafny.Seq.Concat(_dafny.Seq.of(PrettyIns.__default.DecToChar((n).mod(new BigNumber(10)))), _756___accumulator);
          let _in74 = _dafny.EuclideanDivision(n, new BigNumber(10));
          n = _in74;
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
          let _757_formattedAddress;
          _757_formattedAddress = (((((s)[_dafny.ZERO]).dtor_address).isLessThan(Int.__default.TWO__32)) ? (Hex.__default.U32ToHex((((s)[_dafny.ZERO]).dtor_address).toNumber())) : (_dafny.Seq.UnicodeFromString("OutofRange")));
          process.stdout.write((_757_formattedAddress).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(": ")).toVerbatimString(false));
          process.stdout.write((((s)[_dafny.ZERO]).ToString()).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _in75 = (s).slice(_dafny.ONE);
          s = _in75;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static PrintSegments(xs, num) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xs).length))) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("--------------------------------------------\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("Segment ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(num));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _758_k;
          _758_k = ((xs)[_dafny.ZERO]).WeakestPreOperands(_dafny.ZERO);
          let _759_l;
          _759_l = ((xs)[_dafny.ZERO]).WeakestPreCapacity(_dafny.ZERO);
          if ((((xs)[_dafny.ZERO]).is_JUMPSeg) || (((xs)[_dafny.ZERO]).is_JUMPISeg)) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("JUMP/JUMPI: tgt address at the end: ")).toVerbatimString(false));
            let _760_r;
            _760_r = SegBuilder.__default.JUMPResolver((xs)[_dafny.ZERO]);
            let _source49 = _760_r;
            if (_source49.is_Left) {
              let _761___mcc_h0 = (_source49).l;
              let _762_v = _761___mcc_h0;
              let _source50 = _762_v;
              if (_source50.is_Value) {
                let _763___mcc_h2 = (_source50).v;
                let _764_address = _763___mcc_h2;
                process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("0x"), Hex.__default.NatToHex(_764_address))).toVerbatimString(false));
              } else {
                let _765___mcc_h3 = (_source50).s;
                let _766_msg = _765___mcc_h3;
                process.stdout.write((_dafny.Seq.UnicodeFromString("Could not determine stack value")).toVerbatimString(false));
              }
            } else {
              let _767___mcc_h1 = (_source49).r;
              let _768_stackPos = _767___mcc_h1;
              process.stdout.write((_dafny.Seq.UnicodeFromString("Peek(")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_768_stackPos));
              process.stdout.write((_dafny.Seq.UnicodeFromString(")")).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          }
          if (((xs)[_dafny.ZERO]).is_CONTSeg) {
            if ((((((xs)[_dafny.ZERO]).dtor_lastIns).dtor_op).dtor_opcode) !== (EVMConstants.__default.INVALID)) {
              let _769_nextPC;
              _769_nextPC = ((xs)[_dafny.ZERO]).StartAddressNextSeg();
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("CONT: PC of instruction after last is: "), _dafny.Seq.UnicodeFromString(" 0x")), Hex.__default.NatToHex(_769_nextPC)), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
            } else {
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("CONT: has an invaid instructiom"), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("WeakestPre Operands:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(_758_k));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("WeakestPre Capacity:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(_759_l));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("Net Stack Effect:")).toVerbatimString(false));
            process.stdout.write(_dafny.toString(((xs)[_dafny.ZERO]).StackEffect()));
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          }
          PrettyPrinters.__default.PrintInstructions(((xs)[_dafny.ZERO]).Ins());
          let _in76 = (xs).slice(_dafny.ONE);
          let _in77 = (num).plus(_dafny.ONE);
          xs = _in76;
          num = _in77;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static CollectJumpDest(xs) {
      let _770___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_770___accumulator, _dafny.Seq.of());
        } else {
          _770___accumulator = _dafny.Seq.Concat(_770___accumulator, ((xs)[_dafny.ZERO]).CollectJumpDest());
          let _in78 = (xs).slice(_dafny.ONE);
          xs = _in78;
          continue TAIL_CALL_START;
        }
      }
    };
    static CollectJumpDestAsString(xs) {
      let _771___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_771___accumulator, _dafny.Seq.of());
        } else {
          _771___accumulator = _dafny.Seq.Concat(_771___accumulator, _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" ensures s.IsJumpDest(0x"), Hex.__default.NatToHex((xs)[_dafny.ZERO])), _dafny.Seq.UnicodeFromString(" as u256)\n")));
          let _in79 = (xs).slice(_dafny.ONE);
          xs = _in79;
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
      let _772_j;
      _772_j = PrettyPrinters.__default.CollectJumpDestAsString(PrettyPrinters.__default.CollectJumpDest(xs));
      if ((_dafny.ZERO).isLessThan(new BigNumber((_772_j).length))) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("/** Lemma for Jumpdest */")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        process.stdout.write((_772_j).toVerbatimString(false));
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
          let _773_startAddress;
          _773_startAddress = Hex.__default.NatToHex((((((xs)[_dafny.ZERO]).dtor_s).Ins())[_dafny.ZERO]).dtor_address);
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n/** Code starting at 0x")).toVerbatimString(false));
          process.stdout.write((_773_startAddress).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(" */\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("function {:opaque} ExecuteFromTag_")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(num));
          process.stdout.write((_dafny.Seq.UnicodeFromString("(s0: EvmState.ExecutingState): (s': EvmState.State)\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.PC() == 0x")).toVerbatimString(false));
          process.stdout.write((_773_startAddress).toVerbatimString(false));
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
              let _source51 = ((xs)[_dafny.ZERO]).dtor_tgt;
              if (_source51.is_Left) {
                let _774___mcc_h0 = (_source51).l;
                process.stdout.write((_dafny.Seq.UnicodeFromString("")).toVerbatimString(false));
              } else {
                let _775___mcc_h2 = (_source51).r;
                let _776_v = _775___mcc_h2;
                process.stdout.write((_dafny.Seq.UnicodeFromString("  requires s0.IsJumpDest(s0.Peek(")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_776_v));
                process.stdout.write((_dafny.Seq.UnicodeFromString("))\n")).toVerbatimString(false));
              }
            }
          }
          let _source52 = (xs)[_dafny.ZERO];
          if (_source52.is_JUMP) {
            let _777___mcc_h4 = (_source52).s;
            let _778___mcc_h5 = (_source52).wpOp;
            let _779___mcc_h6 = (_source52).wpCap;
            let _780___mcc_h7 = (_source52).tgt;
            let _781___mcc_h8 = (_source52).stacks;
            let _782_tgt = _780___mcc_h7;
            let _783_s = _777___mcc_h4;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.EXECUTING?\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.PC() ==  ")).toVerbatimString(false));
            {
              let _source53 = _782_tgt;
              if (_source53.is_Left) {
                let _784___mcc_h17 = (_source53).l;
                let _785_xc = _784___mcc_h17;
                let _source54 = _785_xc;
                if (_source54.is_Value) {
                  let _786___mcc_h19 = (_source54).v;
                  let _787_v = _786___mcc_h19;
                  process.stdout.write((_dafny.Seq.UnicodeFromString("0x")).toVerbatimString(false));
                  process.stdout.write((Hex.__default.NatToHex((_785_xc).Extract())).toVerbatimString(false));
                } else {
                  let _788___mcc_h21 = (_source54).s;
                  process.stdout.write((_dafny.Seq.UnicodeFromString("Could not extract value ")).toVerbatimString(false));
                }
              } else {
                let _789___mcc_h18 = (_source53).r;
                let _790_v = _789___mcc_h18;
                process.stdout.write((_dafny.Seq.UnicodeFromString("s0.Peek(")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_790_v));
                process.stdout.write((_dafny.Seq.UnicodeFromString(") as nat")).toVerbatimString(false));
              }
            }
            if (((((_783_s).dtor_lastIns).dtor_op).dtor_opcode) === (EVMConstants.__default.JUMPI)) {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" || s'.PC() == 0x")).toVerbatimString(false));
              process.stdout.write((Hex.__default.NatToHex((((_783_s).dtor_lastIns).dtor_address).plus(_dafny.ONE))).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
            let _791_n;
            _791_n = ((xs)[_dafny.ZERO]).StackEffect();
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.Operands() == s0.Operands()")).toVerbatimString(false));
            if ((_dafny.ZERO).isLessThanOrEqualTo(_791_n)) {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" + ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_791_n));
            } else {
              process.stdout.write((_dafny.Seq.UnicodeFromString(" - ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_dafny.ZERO).minus(_791_n)));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          } else if (_source52.is_CONT) {
            let _792___mcc_h9 = (_source52).s;
            let _793___mcc_h10 = (_source52).wpOp;
            let _794___mcc_h11 = (_source52).wpCap;
            let _795___mcc_h12 = (_source52).stacks;
            let _796_s = _792___mcc_h9;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.EXECUTING?\n")).toVerbatimString(false));
            if (((((_796_s).dtor_lastIns).dtor_op).dtor_opcode) !== (EVMConstants.__default.INVALID)) {
              let _797_nextPC;
              _797_nextPC = (_796_s).StartAddressNextSeg();
              process.stdout.write((_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("  ensures s'.PC() == 0x"), Hex.__default.NatToHex(_797_nextPC)), _dafny.Seq.UnicodeFromString("\n"))).toVerbatimString(false));
              let _798_n;
              _798_n = ((xs)[_dafny.ZERO]).StackEffect();
              process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.Operands() == s0.Operands()")).toVerbatimString(false));
              if ((_dafny.ZERO).isLessThanOrEqualTo(_798_n)) {
                process.stdout.write((_dafny.Seq.UnicodeFromString(" + ")).toVerbatimString(false));
                process.stdout.write(_dafny.toString(_798_n));
              } else {
                process.stdout.write((_dafny.Seq.UnicodeFromString(" - ")).toVerbatimString(false));
                process.stdout.write(_dafny.toString((_dafny.ZERO).minus(_798_n)));
              }
            } else {
              process.stdout.write((_dafny.Seq.UnicodeFromString("  Last instruction is invalid")).toVerbatimString(false));
            }
            process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          } else {
            let _799___mcc_h13 = (_source52).s;
            let _800___mcc_h14 = (_source52).wpOp;
            let _801___mcc_h15 = (_source52).wpCap;
            let _802___mcc_h16 = (_source52).stacks;
            let _803_s = _799___mcc_h13;
            process.stdout.write((_dafny.Seq.UnicodeFromString("  ensures s'.RETURNS?\n")).toVerbatimString(false));
          }
          process.stdout.write((_dafny.Seq.UnicodeFromString("{\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  ValidJumpDest(s0);\n")).toVerbatimString(false));
          PrettyPrinters.__default.PrintInstructionsToDafny((((xs)[_dafny.ZERO]).dtor_s).Ins(), _dafny.ZERO);
          process.stdout.write((_dafny.Seq.UnicodeFromString("  s")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(new BigNumber(((((xs)[_dafny.ZERO]).dtor_s).Ins()).length)));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("}\n")).toVerbatimString(false));
          let _in80 = (xs).slice(_dafny.ONE);
          let _in81 = (num).plus(_dafny.ONE);
          xs = _in80;
          num = _in81;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
    static PrintInstructionsToDafny(xs, pos) {
      TAIL_CALL_START: while (true) {
        if ((_dafny.ZERO).isLessThan(new BigNumber((xs).length))) {
          let _804_k;
          _804_k = PrettyIns.__default.PrintInstructionToDafny((xs)[_dafny.ZERO], pos, (pos).plus(_dafny.ONE));
          process.stdout.write((_dafny.Seq.UnicodeFromString("  ")).toVerbatimString(false));
          process.stdout.write((_804_k).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
          let _in82 = (xs).slice(_dafny.ONE);
          let _in83 = (pos).plus(_dafny.ONE);
          xs = _in82;
          pos = _in83;
          continue TAIL_CALL_START;
        }
        return;
        return;
      }
    }
  };
  return $module;
})(); // end of module PrettyPrinters
let CFGState = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "CFGState._default";
    }
    _parentTraits() {
      return [];
    }
    static get DEFAULT__GSTATE() {
      return CFGState.GState.create_EGState(_dafny.ZERO, _dafny.Seq.of());
    };
  };

  $module.GState = class GState {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_EGState(segNum, st) {
      let $dt = new GState(0);
      $dt.segNum = segNum;
      $dt.st = st;
      return $dt;
    }
    static create_ErrorGState(msg) {
      let $dt = new GState(1);
      $dt.msg = msg;
      return $dt;
    }
    get is_EGState() { return this.$tag === 0; }
    get is_ErrorGState() { return this.$tag === 1; }
    get dtor_segNum() { return this.segNum; }
    get dtor_st() { return this.st; }
    get dtor_msg() { return this.msg; }
    toString() {
      if (this.$tag === 0) {
        return "CFGState.GState.EGState" + "(" + _dafny.toString(this.segNum) + ", " + _dafny.toString(this.st) + ")";
      } else if (this.$tag === 1) {
        return "CFGState.GState.ErrorGState" + "(" + this.msg.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.segNum, other.segNum) && _dafny.areEqual(this.st, other.st);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.msg, other.msg);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return CFGState.GState.create_EGState(_dafny.ZERO, _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return GState.Default();
        }
      };
    }
    ToString() {
      let _this = this;
      let _source55 = _this;
      if (_source55.is_EGState) {
        let _805___mcc_h0 = (_source55).segNum;
        let _806___mcc_h1 = (_source55).st;
        let _807_st = _806___mcc_h1;
        let _808_segNum = _805___mcc_h0;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("("), Int.__default.NatToString(_808_segNum)), _dafny.Seq.UnicodeFromString(", [")), StackElement.__default.StackToString(_807_st)), _dafny.Seq.UnicodeFromString("])"));
      } else {
        let _809___mcc_h2 = (_source55).msg;
        let _810_msg = _809___mcc_h2;
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("ErrorGState("), _810_msg), _dafny.Seq.UnicodeFromString(")"));
      }
    };
    IsBounded(n) {
      let _this = this;
      return ((_this).is_ErrorGState) || (((_this).is_EGState) && (((_this).dtor_segNum).isLessThan(n)));
    };
  }
  return $module;
})(); // end of module CFGState
let Automata = (function() {
  let $module = {};


  $module.ValidAuto = class ValidAuto {
    constructor () {
    }
    static get Witness() {
      return Automata.Auto.create_Auto(_dafny.Map.Empty.slice(), _dafny.Seq.of(), _dafny.Map.Empty.slice());
    }
    static get Default() {
      return Automata.ValidAuto.Witness;
    }
  };

  $module.Auto = class Auto {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Auto(transitionsNat, states, indexOf) {
      let $dt = new Auto(0);
      $dt.transitionsNat = transitionsNat;
      $dt.states = states;
      $dt.indexOf = indexOf;
      return $dt;
    }
    get is_Auto() { return this.$tag === 0; }
    get dtor_transitionsNat() { return this.transitionsNat; }
    get dtor_states() { return this.states; }
    get dtor_indexOf() { return this.indexOf; }
    toString() {
      if (this.$tag === 0) {
        return "Automata.Auto.Auto" + "(" + _dafny.toString(this.transitionsNat) + ", " + _dafny.toString(this.states) + ", " + _dafny.toString(this.indexOf) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.transitionsNat, other.transitionsNat) && _dafny.areEqual(this.states, other.states) && _dafny.areEqual(this.indexOf, other.indexOf);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Automata.Auto.create_Auto(_dafny.Map.Empty, _dafny.Seq.of(), _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Auto.Default();
        }
      };
    }
    Equals(b) {
      let _this = this;
      return (((_this).dtor_transitionsNat).equals((b).dtor_transitionsNat)) && (_dafny.areEqual((_this).dtor_states, (b).dtor_states));
    };
    AddState(i) {
      let _this = this;
      let _pat_let_tv0 = i;
      let _pat_let_tv1 = i;
      if (_dafny.Seq.contains((_this).dtor_states, i)) {
        return _this;
      } else {
        let _811_dt__update__tmp_h3 = function (_pat_let0_0) {
          return function (_814_dt__update__tmp_h1) {
            return function (_pat_let3_0) {
              return function (_815_dt__update_hindexOf_h0) {
                return Automata.Auto.create_Auto((_814_dt__update__tmp_h1).dtor_transitionsNat, (_814_dt__update__tmp_h1).dtor_states, _815_dt__update_hindexOf_h0);
              }(_pat_let3_0);
            }(((_this).dtor_indexOf).Merge(_dafny.Map.Empty.slice().updateUnsafe(_pat_let_tv1,new BigNumber(((_this).dtor_states).length))));
          }(_pat_let0_0);
        }(function (_pat_let1_0) {
          return function (_812_dt__update__tmp_h0) {
            return function (_pat_let2_0) {
              return function (_813_dt__update_hstates_h0) {
                return Automata.Auto.create_Auto((_812_dt__update__tmp_h0).dtor_transitionsNat, _813_dt__update_hstates_h0, (_812_dt__update__tmp_h0).dtor_indexOf);
              }(_pat_let2_0);
            }(_dafny.Seq.Concat((_this).dtor_states, _dafny.Seq.of(_pat_let_tv0)));
          }(_pat_let1_0);
        }(_this));
        let _816_dt__update_htransitionsNat_h0 = ((_this).dtor_transitionsNat).Merge(_dafny.Map.Empty.slice().updateUnsafe(new BigNumber(((_this).dtor_states).length),_dafny.Seq.of()));
        return Automata.Auto.create_Auto(_816_dt__update_htransitionsNat_h0, (_811_dt__update__tmp_h3).dtor_states, (_811_dt__update__tmp_h3).dtor_indexOf);
      }
    };
    AddStates(xs) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _this;
        } else {
          let _in84 = (_this).AddState((xs)[_dafny.ZERO]);
          let _in85 = (xs).slice(_dafny.ONE);
          _this = _in84;
          ;
          xs = _in85;
          continue TAIL_CALL_START;
        }
      }
    };
    AddEdge(i, j) {
      let _this = this;
      let _pat_let_tv2 = i;
      let _pat_let_tv3 = i;
      let _pat_let_tv4 = j;
      let _817_a1 = ((_this).AddState(i)).AddState(j);
      if (_dafny.Seq.contains(((_817_a1).dtor_transitionsNat).get(((_817_a1).dtor_indexOf).get(i)), ((_817_a1).dtor_indexOf).get(j))) {
        return _817_a1;
      } else {
        let _818_w = function (_pat_let4_0) {
          return function (_819_dt__update__tmp_h1) {
            return function (_pat_let5_0) {
              return function (_820_dt__update_htransitionsNat_h0) {
                return Automata.Auto.create_Auto(_820_dt__update_htransitionsNat_h0, (_819_dt__update__tmp_h1).dtor_states, (_819_dt__update__tmp_h1).dtor_indexOf);
              }(_pat_let5_0);
            }(((_817_a1).dtor_transitionsNat).Merge(_dafny.Map.Empty.slice().updateUnsafe(((_817_a1).dtor_indexOf).get(_pat_let_tv2),_dafny.Seq.Concat(((_817_a1).dtor_transitionsNat).get(((_817_a1).dtor_indexOf).get(_pat_let_tv3)), _dafny.Seq.of(((_817_a1).dtor_indexOf).get(_pat_let_tv4))))));
          }(_pat_let4_0);
        }(_817_a1);
        return _818_w;
      }
    };
    AddEdges(i, js, index) {
      let _this = this;
      if ((new BigNumber((js).length)).isEqualTo(index)) {
        return (_this).AddState(i);
      } else {
        let _821_a1 = (_this).AddEdge(i, (js)[index]);
        let _822_a2 = (_821_a1).AddEdges(i, js, (index).plus(_dafny.ONE));
        return _822_a2;
      }
    };
    SSize() {
      let _this = this;
      return new BigNumber(((_this).dtor_states).length);
    };
    TSize(index) {
      let _this = this;
      let _823___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((index).isEqualTo(new BigNumber(((_this).dtor_states).length))) {
          return (_dafny.ZERO).plus(_823___accumulator);
        } else {
          _823___accumulator = (_823___accumulator).plus(new BigNumber((((_this).dtor_transitionsNat).get(index)).length));
          let _in86 = _this;
          let _in87 = (index).plus(_dafny.ONE);
          _this = _in86;
          ;
          index = _in87;
          continue TAIL_CALL_START;
        }
      }
    };
    Succ(s) {
      let _this = this;
      return _dafny.Seq.Create(new BigNumber((((_this).dtor_transitionsNat).get(((_this).dtor_indexOf).get(s))).length), ((_824_s) => function (_825_i) {
        return ((_this).dtor_states)[(((_this).dtor_transitionsNat).get(((_this).dtor_indexOf).get(_824_s)))[_825_i]];
      })(s));
    };
    SuccNat(i) {
      let _this = this;
      return ((_this).dtor_transitionsNat).get(i);
    };
    ToDot(nodeToString, labelToString, prefix, name) {
      let _this = this;
      process.stdout.write((_dafny.Seq.UnicodeFromString("// Number of states: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString((_this).SSize()));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("// Number of transitions : ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString((_this).TSize(_dafny.ZERO)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("digraph G {\n")).toVerbatimString(false));
      process.stdout.write((prefix).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      let _hi0 = new BigNumber(((_this).dtor_states).length);
      for (let _826_i = _dafny.ZERO; _826_i.isLessThan(_hi0); _826_i = _826_i.plus(_dafny.ONE)) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("s_")).toVerbatimString(false));
        process.stdout.write(_dafny.toString(_826_i));
        process.stdout.write((_dafny.Seq.UnicodeFromString(" [label=")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.Concat((nodeToString)(((_this).dtor_states)[_826_i]), _dafny.Seq.UnicodeFromString("]\n"))).toVerbatimString(false));
      }
      let _hi1 = new BigNumber(((_this).dtor_states).length);
      for (let _827_i = _dafny.ZERO; _827_i.isLessThan(_hi1); _827_i = _827_i.plus(_dafny.ONE)) {
        let _hi2 = new BigNumber((((_this).dtor_transitionsNat).get(_827_i)).length);
        for (let _828_j = _dafny.ZERO; _828_j.isLessThan(_hi2); _828_j = _828_j.plus(_dafny.ONE)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("s_")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(_827_i));
          process.stdout.write((_dafny.Seq.UnicodeFromString(" -> ")).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString("s_")).toVerbatimString(false));
          process.stdout.write(_dafny.toString((((_this).dtor_transitionsNat).get(_827_i))[_828_j]));
          process.stdout.write(((labelToString)(((_this).dtor_states)[_827_i], _828_j, ((_this).dtor_states)[(((_this).dtor_transitionsNat).get(_827_i))[_828_j]])).toVerbatimString(false));
          process.stdout.write((_dafny.Seq.UnicodeFromString(";\n")).toVerbatimString(false));
        }
      }
      process.stdout.write((_dafny.Seq.UnicodeFromString("}\n")).toVerbatimString(false));
      return;
    }
  }
  return $module;
})(); // end of module Automata
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
      let _829___accumulator = _dafny.Set.fromElements();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.Set.fromElements()).Union(_829___accumulator);
        } else {
          _829___accumulator = (_829___accumulator).Union((xs)[_dafny.ZERO]);
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
    static SplitSet(xs, f) {
      let _830_asSeq = SeqOfSets.__default.SetToSequence(xs);
      return SeqOfSets.__default.SplitSeqTail(_830_asSeq, f, _dafny.Set.fromElements(), _dafny.Set.fromElements(), _dafny.ZERO);
    };
    static SplitSeqOfSet(xs, f) {
      let _831___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_831___accumulator, _dafny.Seq.of());
        } else {
          _831___accumulator = _dafny.Seq.Concat(_831___accumulator, _dafny.Seq.of(SeqOfSets.__default.SplitSet((xs)[_dafny.ZERO], f)));
          let _in89 = (xs).slice(_dafny.ONE);
          let _in90 = f;
          xs = _in89;
          f = _in90;
          continue TAIL_CALL_START;
        }
      }
    };
    static SetToSequence(s) {
      let _832___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv5 = s;
        if ((s).equals(_dafny.Set.fromElements())) {
          return _dafny.Seq.Concat(_832___accumulator, _dafny.Seq.of());
        } else {
          return function (_let_dummy_6) {
            let _833_x = undefined;
            L_ASSIGN_SUCH_THAT_0: {
              for (const _assign_such_that_0 of (s).Elements) {
                _833_x = _assign_such_that_0;
                if (((s).contains(_833_x)) && (_dafny.Quantifier((s).Elements, true, function (_forall_var_9) {
                  let _834_y = _forall_var_9;
                  return !((s).contains(_834_y)) || ((_833_x).isLessThanOrEqualTo(_834_y));
                }))) {
                  break L_ASSIGN_SUCH_THAT_0;
                }
              }
              throw new Error("assign-such-that search produced no value (line 218)");
            }
            return _dafny.Seq.Concat(_dafny.Seq.of(_833_x), SeqOfSets.__default.SetToSequence((_pat_let_tv5).Difference(_dafny.Set.fromElements(_833_x))));
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
    static MakeInit(n) {
      let _835_s = function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of _dafny.IntegerRange(_dafny.ZERO, n)) {
          let _836_q = _compr_0;
          if (((_dafny.ZERO).isLessThanOrEqualTo(_836_q)) && ((_836_q).isLessThan(n))) {
            _coll0.add(_836_q);
          }
        }
        return _coll0;
      }();
      return PartitionMod.Partition.create_Partition(n, _dafny.Seq.of(_835_s));
    };
    static SplitTrueAndFalse(xs, equiv, n) {
      let _837___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _838_first = (SeqOfSets.__default.SetToSequence(xs))[_dafny.ZERO];
        let _839_xsTrue = function () {
          let _coll1 = new _dafny.Set();
          for (const _compr_1 of (xs).Elements) {
            let _840_x = _compr_1;
            if (((xs).contains(_840_x)) && ((equiv)(_838_first, _840_x))) {
              _coll1.add(_840_x);
            }
          }
          return _coll1;
        }();
        let _841_xsFalse = (xs).Difference(_839_xsTrue);
        if ((_841_xsFalse).equals(_dafny.Set.fromElements())) {
          return _dafny.Seq.Concat(_837___accumulator, _dafny.Seq.of(_839_xsTrue));
        } else {
          _837___accumulator = _dafny.Seq.Concat(_837___accumulator, _dafny.Seq.of(_839_xsTrue));
          let _in101 = _841_xsFalse;
          let _in102 = equiv;
          let _in103 = n;
          xs = _in101;
          equiv = _in102;
          n = _in103;
          continue TAIL_CALL_START;
        }
      }
    };
    static SplitAllClasses(xs, equiv, n) {
      return _dafny.Seq.Create(new BigNumber((xs).length), ((_842_xs, _843_equiv, _844_n) => function (_845_i) {
        return PartitionMod.__default.SplitTrueAndFalse((_842_xs)[_845_i], _843_equiv, _844_n);
      })(xs, equiv, n));
    };
    static PrintPartition(p) {
      let _hi3 = new BigNumber(((p).dtor_elem).length);
      for (let _846_k = _dafny.ZERO; _846_k.isLessThan(_hi3); _846_k = _846_k.plus(_dafny.ONE)) {
        let _847_setToSeq;
        _847_setToSeq = SeqOfSets.__default.SetToSequence(((p).dtor_elem)[_846_k]);
        process.stdout.write(_dafny.toString(_847_setToSeq));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      return;
    }
  };

  $module.ValidPartition = class ValidPartition {
    constructor () {
    }
    static get Witness() {
      return PartitionMod.__default.MakeInit(_dafny.ONE);
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
    SplitIn2(f) {
      let _this = this;
      let _848_sTrue = function () {
        let _coll2 = new _dafny.Set();
        for (const _compr_2 of (SeqOfSets.__default.SetU((_this).dtor_elem)).Elements) {
          let _849_q = _compr_2;
          if (((SeqOfSets.__default.SetU((_this).dtor_elem)).contains(_849_q)) && ((f)(_849_q))) {
            _coll2.add(_849_q);
          }
        }
        return _coll2;
      }();
      let _850_sFalse = (SeqOfSets.__default.SetU((_this).dtor_elem)).Difference(_848_sTrue);
      let _851_d = _dafny.Seq.Concat(((!(_848_sTrue).equals(_dafny.Set.fromElements())) ? (_dafny.Seq.of(_848_sTrue)) : (_dafny.Seq.of())), ((!(_850_sFalse).equals(_dafny.Set.fromElements())) ? (_dafny.Seq.of(_850_sFalse)) : (_dafny.Seq.of())));
      let _852_e = function (_pat_let7_0) {
        return function (_853_dt__update__tmp_h0) {
          return function (_pat_let8_0) {
            return function (_854_dt__update_helem_h0) {
              return PartitionMod.Partition.create_Partition((_853_dt__update__tmp_h0).dtor_n, _854_dt__update_helem_h0);
            }(_pat_let8_0);
          }(_851_d);
        }(_pat_let7_0);
      }(_this);
      return _852_e;
    };
    ComputeFinest(equiv) {
      let _this = this;
      let _855_k = PartitionMod.__default.SplitTrueAndFalse(SeqOfSets.__default.SetU((_this).dtor_elem), equiv, (_this).dtor_n);
      let _856_dt__update__tmp_h0 = _this;
      let _857_dt__update_helem_h0 = _855_k;
      return PartitionMod.Partition.create_Partition((_856_dt__update__tmp_h0).dtor_n, _857_dt__update_helem_h0);
    };
    RefineAll(equiv) {
      let _this = this;
      let _858_k = PartitionMod.__default.SplitAllClasses((_this).dtor_elem, equiv, (_this).dtor_n);
      let _859_d = MiscTypes.__default.Flatten(_858_k);
      let _860_e = function (_pat_let9_0) {
        return function (_861_dt__update__tmp_h0) {
          return function (_pat_let10_0) {
            return function (_862_dt__update_helem_h0) {
              return PartitionMod.Partition.create_Partition((_861_dt__update__tmp_h0).dtor_n, _862_dt__update_helem_h0);
            }(_pat_let10_0);
          }(_859_d);
        }(_pat_let9_0);
      }(_this);
      return _860_e;
    };
    GetClass(x, index) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((((_this).dtor_elem)[index]).contains(x)) {
          return index;
        } else {
          let _in104 = _this;
          let _in105 = x;
          let _in106 = (index).plus(_dafny.ONE);
          _this = _in104;
          ;
          x = _in105;
          index = _in106;
          continue TAIL_CALL_START;
        }
      }
    };
    GetClassRepOf(x) {
      let _this = this;
      let _863_c = (_this).GetClass(x, _dafny.ZERO);
      return (SeqOfSets.__default.SetToSequence(((_this).dtor_elem)[_863_c]))[_dafny.ZERO];
    };
    GetClassRepOfSeqs(xs) {
      let _this = this;
      let _864___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_864___accumulator, _dafny.Seq.of());
        } else {
          _864___accumulator = _dafny.Seq.Concat(_864___accumulator, _dafny.Seq.of((_this).GetClassRepOf((xs)[_dafny.ZERO])));
          let _in107 = _this;
          let _in108 = (xs).slice(_dafny.ONE);
          _this = _in107;
          ;
          xs = _in108;
          continue TAIL_CALL_START;
        }
      }
    };
  }
  return $module;
})(); // end of module PartitionMod
let GStateMinimiser = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "GStateMinimiser._default";
    }
    _parentTraits() {
      return [];
    }
    static MakeInit(aut, clazz) {
      return GStateMinimiser.Pair.create_Pair(aut, clazz);
    };
    static get DEFAULT__STATE() {
      return CFGState.__default.DEFAULT__GSTATE;
    };
  };

  $module.ValidPair = class ValidPair {
    constructor () {
    }
    static get Witness() {
      return GStateMinimiser.Pair.create_Pair((Automata.Auto.create_Auto(_dafny.Map.Empty.slice(), _dafny.Seq.of(), _dafny.Map.Empty.slice())).AddState(GStateMinimiser.__default.DEFAULT__STATE), PartitionMod.__default.MakeInit(_dafny.ONE));
    }
    static get Default() {
      return GStateMinimiser.ValidPair.Witness;
    }
  };

  $module.Pair = class Pair {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pair(aut, clazz) {
      let $dt = new Pair(0);
      $dt.aut = aut;
      $dt.clazz = clazz;
      return $dt;
    }
    get is_Pair() { return this.$tag === 0; }
    get dtor_aut() { return this.aut; }
    get dtor_clazz() { return this.clazz; }
    toString() {
      if (this.$tag === 0) {
        return "GStateMinimiser.Pair.Pair" + "(" + _dafny.toString(this.aut) + ", " + _dafny.toString(this.clazz) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.aut, other.aut) && _dafny.areEqual(this.clazz, other.clazz);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return GStateMinimiser.Pair.create_Pair(Automata.ValidAuto.Default, PartitionMod.ValidPartition.Default);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Pair.Default();
        }
      };
    }
    ClassSucc(x) {
      let _this = this;
      let _865_l = ((_this).dtor_aut).SuccNat(x);
      return _dafny.Seq.Create(new BigNumber((_865_l).length), ((_866_l) => function (_867_z) {
        return ((_this).dtor_clazz).GetClass((_866_l)[_867_z], _dafny.ZERO);
      })(_865_l));
    };
    ClassSplitter() {
      let _this = this;
      let _868_dt__update__tmp_h0 = _this;
      let _869_dt__update_hclazz_h0 = ((_this).dtor_clazz).RefineAll(_this.Splitter.bind(_this));
      return GStateMinimiser.Pair.create_Pair((_868_dt__update__tmp_h0).dtor_aut, _869_dt__update_hclazz_h0);
    };
    Splitter(x, y) {
      let _this = this;
      return _dafny.areEqual((_this).ClassSucc(x), (_this).ClassSucc(y));
    };
    Minimise() {
      let _this = this;
      let _870_p1 = GStateMinimiser.Pair.IterSplit(_this);
      return (_870_p1).MapToClasses(Automata.Auto.create_Auto(_dafny.Map.Empty.slice(), _dafny.Seq.of(), _dafny.Map.Empty.slice()), _dafny.ZERO);
    };
    MapToClasses(acc, index) {
      let _this = this;
      if ((index).isEqualTo(new BigNumber((((_this).dtor_aut).dtor_states).length))) {
        return acc;
      } else {
        let _871_succs = MiscTypes.__default.MapP(((_this).dtor_clazz).GetClassRepOfSeqs((((_this).dtor_aut).dtor_transitionsNat).get(index)), function (_872_i) {
          return (((_this).dtor_aut).dtor_states)[_872_i];
        });
        let _873_a_k = (_this).MapToClasses((acc).AddEdges((((_this).dtor_aut).dtor_states)[((_this).dtor_clazz).GetClassRepOf(index)], _871_succs, _dafny.ZERO), (index).plus(_dafny.ONE));
        return _873_a_k;
      }
    };
    static IterSplit(pp) {
      TAIL_CALL_START: while (true) {
        let _874_p1 = (pp).ClassSplitter();
        if ((new BigNumber((((_874_p1).dtor_clazz).dtor_elem).length)).isEqualTo(new BigNumber((((pp).dtor_clazz).dtor_elem).length))) {
          return pp;
        } else {
          let _in109 = _874_p1;
          pp = _in109;
          continue TAIL_CALL_START;
        }
      }
    };
  }
  return $module;
})(); // end of module GStateMinimiser
let Statistics = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Statistics._default";
    }
    _parentTraits() {
      return [];
    }
    static get DEFAULT__STATS() {
      return Statistics.Stats.create_Stats(false, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.Tuple.of(_dafny.ZERO, _dafny.ZERO));
    };
  };

  $module.Stats = class Stats {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Stats(maxDepthReached, visitedStates, wPreInvSuccess, errorState, nonMinimisedSize) {
      let $dt = new Stats(0);
      $dt.maxDepthReached = maxDepthReached;
      $dt.visitedStates = visitedStates;
      $dt.wPreInvSuccess = wPreInvSuccess;
      $dt.errorState = errorState;
      $dt.nonMinimisedSize = nonMinimisedSize;
      return $dt;
    }
    get is_Stats() { return this.$tag === 0; }
    get dtor_maxDepthReached() { return this.maxDepthReached; }
    get dtor_visitedStates() { return this.visitedStates; }
    get dtor_wPreInvSuccess() { return this.wPreInvSuccess; }
    get dtor_errorState() { return this.errorState; }
    get dtor_nonMinimisedSize() { return this.nonMinimisedSize; }
    toString() {
      if (this.$tag === 0) {
        return "Statistics.Stats.Stats" + "(" + _dafny.toString(this.maxDepthReached) + ", " + _dafny.toString(this.visitedStates) + ", " + _dafny.toString(this.wPreInvSuccess) + ", " + _dafny.toString(this.errorState) + ", " + _dafny.toString(this.nonMinimisedSize) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && this.maxDepthReached === other.maxDepthReached && _dafny.areEqual(this.visitedStates, other.visitedStates) && _dafny.areEqual(this.wPreInvSuccess, other.wPreInvSuccess) && _dafny.areEqual(this.errorState, other.errorState) && _dafny.areEqual(this.nonMinimisedSize, other.nonMinimisedSize);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Statistics.Stats.create_Stats(false, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.Tuple.Default(_dafny.ZERO, _dafny.ZERO));
    }
    static Rtd() {
      return class {
        static get Default() {
          return Stats.Default();
        }
      };
    }
    SetMaxDepth() {
      let _this = this;
      let _875_dt__update__tmp_h0 = _this;
      let _876_dt__update_hmaxDepthReached_h0 = true;
      return Statistics.Stats.create_Stats(_876_dt__update_hmaxDepthReached_h0, (_875_dt__update__tmp_h0).dtor_visitedStates, (_875_dt__update__tmp_h0).dtor_wPreInvSuccess, (_875_dt__update__tmp_h0).dtor_errorState, (_875_dt__update__tmp_h0).dtor_nonMinimisedSize);
    };
    IncVisited() {
      let _this = this;
      let _877_dt__update__tmp_h0 = _this;
      let _878_dt__update_hvisitedStates_h0 = ((_this).dtor_visitedStates).plus(_dafny.ONE);
      return Statistics.Stats.create_Stats((_877_dt__update__tmp_h0).dtor_maxDepthReached, _878_dt__update_hvisitedStates_h0, (_877_dt__update__tmp_h0).dtor_wPreInvSuccess, (_877_dt__update__tmp_h0).dtor_errorState, (_877_dt__update__tmp_h0).dtor_nonMinimisedSize);
    };
    IncWpre() {
      let _this = this;
      let _879_dt__update__tmp_h0 = _this;
      let _880_dt__update_hwPreInvSuccess_h0 = ((_this).dtor_wPreInvSuccess).plus(_dafny.ONE);
      return Statistics.Stats.create_Stats((_879_dt__update__tmp_h0).dtor_maxDepthReached, (_879_dt__update__tmp_h0).dtor_visitedStates, _880_dt__update_hwPreInvSuccess_h0, (_879_dt__update__tmp_h0).dtor_errorState, (_879_dt__update__tmp_h0).dtor_nonMinimisedSize);
    };
    IncError() {
      let _this = this;
      let _881_dt__update__tmp_h0 = _this;
      let _882_dt__update_herrorState_h0 = ((_this).dtor_errorState).plus(_dafny.ONE);
      return Statistics.Stats.create_Stats((_881_dt__update__tmp_h0).dtor_maxDepthReached, (_881_dt__update__tmp_h0).dtor_visitedStates, (_881_dt__update__tmp_h0).dtor_wPreInvSuccess, _882_dt__update_herrorState_h0, (_881_dt__update__tmp_h0).dtor_nonMinimisedSize);
    };
    PrettyPrint() {
      let _this = this;
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("MaxDepth reached:"), (((_this).dtor_maxDepthReached) ? (_dafny.Seq.UnicodeFromString("true")) : (_dafny.Seq.UnicodeFromString("false")))), _dafny.Seq.UnicodeFromString("\n")), _dafny.Seq.UnicodeFromString("ErrorStates reached:")), Int.__default.NatToString((_this).dtor_errorState)), _dafny.Seq.UnicodeFromString("\n")), _dafny.Seq.UnicodeFromString("States seen:")), Int.__default.NatToString((_this).dtor_visitedStates)), _dafny.Seq.UnicodeFromString("\n")), _dafny.Seq.UnicodeFromString("WPre success:")), Int.__default.NatToString((_this).dtor_wPreInvSuccess)), _dafny.Seq.UnicodeFromString("\n"));
    };
  }
  return $module;
})(); // end of module Statistics
let HTML = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "HTML._default";
    }
    _parentTraits() {
      return [];
    }
    static Font(s, colour) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<FONT"), ((!_dafny.areEqual(colour, _dafny.Seq.UnicodeFromString(""))) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" COLOR=\""), colour), _dafny.Seq.UnicodeFromString("\"> "))) : (_dafny.Seq.UnicodeFromString("> ")))), s), _dafny.Seq.UnicodeFromString("</FONT>"));
    };
    static RowTR(s) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TR>"), s), _dafny.Seq.UnicodeFromString("</TR>\n"));
    };
    static CellTD(body, align, border, sides, colspan, rowspan, bgcolour, cellspacing, cellpadding) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TD "), _dafny.Seq.UnicodeFromString("ALIGN=\"")), align), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("BORDER=\"")), border), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("SIDES=\"")), sides), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("BGCOLOR=\"")), bgcolour), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("CELLPADDING=\"")), cellpadding), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("CELLSPACING=\"")), cellspacing), _dafny.Seq.UnicodeFromString("\" ")), ((!_dafny.areEqual(colspan, _dafny.Seq.UnicodeFromString("0"))) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("COLSPAN=\""), colspan), _dafny.Seq.UnicodeFromString("\" "))) : (_dafny.Seq.UnicodeFromString("")))), ((!_dafny.areEqual(rowspan, _dafny.Seq.UnicodeFromString("1"))) ? (_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("ROWSPAN=\""), rowspan), _dafny.Seq.UnicodeFromString("\" "))) : (_dafny.Seq.UnicodeFromString("")))), _dafny.Seq.UnicodeFromString(">")), body), _dafny.Seq.UnicodeFromString("</TD>\n"));
    };
    static Table(body, colour, bgcolour, cellborder, border, cellpadding, cellspacing) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TABLE "), _dafny.Seq.UnicodeFromString("BORDER=\"")), border), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("CELLBORDER=\"")), cellborder), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("CELLPADDING=\"")), cellpadding), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("CELLSPACING=\"")), cellspacing), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("BGCOLOR=\"")), bgcolour), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString("COLOR=\"")), colour), _dafny.Seq.UnicodeFromString("\" ")), _dafny.Seq.UnicodeFromString(">")), body), _dafny.Seq.UnicodeFromString("</TABLE>\n"));
    };
    static DOTSeg(s, numSeg) {
      let _883_jumpTip = ((((s).is_JUMPSeg) || ((s).is_JUMPISeg)) ? (function (_pat_let11_0) {
        return function (_884_r) {
          return function (_source56) {
            if (_source56.is_Left) {
              let _885___mcc_h0 = (_source56).l;
              let _886_v = _885___mcc_h0;
              let _source57 = _886_v;
              if (_source57.is_Value) {
                let _887___mcc_h2 = (_source57).v;
                let _888_address = _887___mcc_h2;
                return _dafny.Seq.Concat(_dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Constant 0x")), Hex.__default.NatToHex(_888_address));
              } else {
                let _889___mcc_h3 = (_source57).s;
                let _890_msg = _889___mcc_h3;
                return _dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Unknown"));
              }
            } else {
              let _891___mcc_h1 = (_source56).r;
              let _892_stackPos = _891___mcc_h1;
              return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Stack on Entry.Peek(")), Int.__default.NatToString(_892_stackPos)), _dafny.Seq.UnicodeFromString(")"));
            }
          }(_884_r);
        }(_pat_let11_0);
      }(SegBuilder.__default.JUMPResolver(s))) : (_dafny.Seq.UnicodeFromString("")));
      let _893_stackSizeEffect = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Stack Size "), HTML.__default.DELTA__SYMBOL), _dafny.Seq.UnicodeFromString(" : ")), Int.__default.IntToString((s).StackEffect()));
      let _894_mninNumOpe = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Stack Size on Entry ")), HTML.__default.LARGER__OR__EQ__SYMBOL), _dafny.Seq.UnicodeFromString(" ")), Int.__default.NatToString((s).WeakestPreOperands(_dafny.ZERO)));
      let _895_prefix = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<B>Segment "), Int.__default.NatToString(numSeg)), _dafny.Seq.UnicodeFromString(" [0x")), Hex.__default.NatToHex((s).StartAddress())), _dafny.Seq.UnicodeFromString("]</B><BR ALIGN=\"CENTER\"/>\n"));
      let _896_body = Instructions.__default.ToDot((s).Ins());
      return _dafny.Tuple.of(_dafny.Seq.Concat(_895_prefix, _896_body), _dafny.Seq.Concat(_dafny.Seq.Concat(_893_stackSizeEffect, _883_jumpTip), _894_mninNumOpe));
    };
    static DOTSegTable(s, numSeg) {
      let _897_jumpTip = ((((s).is_JUMPSeg) || ((s).is_JUMPISeg)) ? (function (_pat_let12_0) {
        return function (_898_r) {
          return function (_source58) {
            if (_source58.is_Left) {
              let _899___mcc_h0 = (_source58).l;
              let _900_v = _899___mcc_h0;
              let _source59 = _900_v;
              if (_source59.is_Value) {
                let _901___mcc_h2 = (_source59).v;
                let _902_address = _901___mcc_h2;
                return _dafny.Seq.Concat(_dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Constant 0x")), Hex.__default.NatToHex(_902_address));
              } else {
                let _903___mcc_h3 = (_source59).s;
                let _904_msg = _903___mcc_h3;
                return _dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Unknown"));
              }
            } else {
              let _905___mcc_h1 = (_source58).r;
              let _906_stackPos = _905___mcc_h1;
              return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(HTML.__default.LINE__FEED__SYMBOL, _dafny.Seq.UnicodeFromString("Exit Jump target: Stack on Entry.Peek(")), Int.__default.NatToString(_906_stackPos)), _dafny.Seq.UnicodeFromString(")"));
            }
          }(_898_r);
        }(_pat_let12_0);
      }(SegBuilder.__default.JUMPResolver(s))) : (_dafny.Seq.UnicodeFromString("")));
      let _907_tableStart = _dafny.Seq.UnicodeFromString("<TABLE ALIGN=\"LEFT\" CELLBORDER=\"0\" BORDER=\"0\" cellpadding=\"0\"  CELLSPACING=\"1\">\n");
      let _908_prefix = _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<TR><TD "), _dafny.Seq.UnicodeFromString(">Segment ")), Int.__default.NatToString(numSeg)), _dafny.Seq.UnicodeFromString(" [0x")), Hex.__default.NatToHex((s).StartAddress())), _dafny.Seq.UnicodeFromString("]</TD>")), _dafny.Seq.UnicodeFromString("<TD")), _dafny.Seq.UnicodeFromString(" href=\"\" tooltip=\"Stack Size ")), HTML.__default.DELTA__SYMBOL), _dafny.Seq.UnicodeFromString(": ")), Int.__default.IntToString((s).StackEffect())), HTML.__default.LINE__FEED__SYMBOL), _dafny.Seq.UnicodeFromString("Stack Size on Entry ")), HTML.__default.LARGER__OR__EQ__SYMBOL), _dafny.Seq.UnicodeFromString(" ")), Int.__default.NatToString((s).WeakestPreOperands(_dafny.ZERO))), _897_jumpTip), _dafny.Seq.UnicodeFromString("\"")), _dafny.Seq.UnicodeFromString("><FONT color=\"green\">")), HTML.__default.INFO__SYMBOL), _dafny.Seq.UnicodeFromString("</FONT></TD>")), _dafny.Seq.UnicodeFromString("</TR><HR/>\n"));
      let _909_tableEnd = _dafny.Seq.UnicodeFromString("</TABLE>\n");
      let _910_body = HTML.__default.DOTInsTable((s).Ins(), true);
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_907_tableStart, _908_prefix), _910_body), _909_tableEnd);
    };
    static DOTInsTable(xi, isFirst) {
      let _911___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xi).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_911___accumulator, _dafny.Seq.UnicodeFromString(""));
        } else {
          let _912_prefix = _dafny.Seq.UnicodeFromString("<TR><TD width=\"1\" fixedsize=\"true\" align=\"left\">\n");
          let _913_suffix = _dafny.Seq.UnicodeFromString("</TD></TR>\n");
          let _914_exitPortTag = ((((xi)[_dafny.ZERO]).IsJump()) ? (_dafny.Seq.UnicodeFromString("PORT=\"exit\"")) : (_dafny.Seq.UnicodeFromString("")));
          let _915_entryPortTag = ((isFirst) ? (_dafny.Seq.UnicodeFromString("PORT=\"entry\"")) : (_dafny.Seq.UnicodeFromString("")));
          let _916_a = ((xi)[_dafny.ZERO]).ToHTMLTable(_915_entryPortTag, _914_exitPortTag);
          _911___accumulator = _dafny.Seq.Concat(_911___accumulator, _dafny.Seq.Concat(_dafny.Seq.Concat(_912_prefix, _916_a), _913_suffix));
          let _in110 = (xi).slice(_dafny.ONE);
          let _in111 = false;
          xi = _in110;
          isFirst = _in111;
          continue TAIL_CALL_START;
        }
      }
    };
    static get LINE__FEED__SYMBOL() {
      return _dafny.Seq.UnicodeFromString("&#10;");
    };
    static get DELTA__SYMBOL() {
      return _dafny.Seq.UnicodeFromString("&#916;");
    };
    static get LARGER__OR__EQ__SYMBOL() {
      return _dafny.Seq.UnicodeFromString("&#8805;");
    };
    static get INFO__SYMBOL() {
      return _dafny.Seq.UnicodeFromString("&#8505;&#65039;");
    };
    static get WHITE__SPACE__SYMBOL() {
      return _dafny.Seq.UnicodeFromString("&#160;");
    };
  };
  return $module;
})(); // end of module HTML
let EVMObject = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "EVMObject._default";
    }
    _parentTraits() {
      return [];
    }
    static CollectJumpDests(xs) {
      let _917___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_917___accumulator, _dafny.Seq.of());
        } else {
          _917___accumulator = _dafny.Seq.Concat(_917___accumulator, ((xs)[_dafny.ZERO]).CollectJumpDest());
          let _in112 = (xs).slice(_dafny.ONE);
          xs = _in112;
          continue TAIL_CALL_START;
        }
      }
    };
    static CollectThem(xs) {
      return EVMObject.__default.CollectPCToSeg(xs, _dafny.Map.Empty.slice(), _dafny.ZERO);
    };
    static CollectPCToSeg(xs, m, index) {
      TAIL_CALL_START: while (true) {
        if ((index).isEqualTo(new BigNumber((xs).length))) {
          return m;
        } else {
          let _in113 = xs;
          let _in114 = (m).update(((xs)[index]).StartAddress(), index);
          let _in115 = (index).plus(_dafny.ONE);
          xs = _in113;
          m = _in114;
          index = _in115;
          continue TAIL_CALL_START;
        }
      }
    };
  };

  $module.Path = class Path {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Path(states, exits) {
      let $dt = new Path(0);
      $dt.states = states;
      $dt.exits = exits;
      return $dt;
    }
    get is_Path() { return this.$tag === 0; }
    get dtor_states() { return this.states; }
    get dtor_exits() { return this.exits; }
    toString() {
      if (this.$tag === 0) {
        return "EVMObject.Path.Path" + "(" + _dafny.toString(this.states) + ", " + _dafny.toString(this.exits) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.states, other.states) && _dafny.areEqual(this.exits, other.exits);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return EVMObject.Path.create_Path(_dafny.Seq.of(), _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return Path.Default();
        }
      };
    }
  }

  $module.ValidSeqValidLinSeg = class ValidSeqValidLinSeg {
    constructor () {
    }
    static get Default() {
      return _dafny.Seq.of();
    }
  };

  $module.ValidEVMObj = class ValidEVMObj {
    constructor () {
    }
    static get Witness() {
      return EVMObject.EVMObj.create_EVMObj(_dafny.Seq.of(), _dafny.Seq.of(), EVMObject.__default.CollectThem(_dafny.Seq.of()));
    }
    static get Default() {
      return EVMObject.ValidEVMObj.Witness;
    }
  };

  $module.EVMObj = class EVMObj {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_EVMObj(xs, jumpDests, PCToSegMap) {
      let $dt = new EVMObj(0);
      $dt.xs = xs;
      $dt.jumpDests = jumpDests;
      $dt.PCToSegMap = PCToSegMap;
      return $dt;
    }
    get is_EVMObj() { return this.$tag === 0; }
    get dtor_xs() { return this.xs; }
    get dtor_jumpDests() { return this.jumpDests; }
    get dtor_PCToSegMap() { return this.PCToSegMap; }
    toString() {
      if (this.$tag === 0) {
        return "EVMObject.EVMObj.EVMObj" + "(" + _dafny.toString(this.xs) + ", " + _dafny.toString(this.jumpDests) + ", " + _dafny.toString(this.PCToSegMap) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.xs, other.xs) && _dafny.areEqual(this.jumpDests, other.jumpDests) && _dafny.areEqual(this.PCToSegMap, other.PCToSegMap);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return EVMObject.EVMObj.create_EVMObj(_dafny.Seq.of(), _dafny.Seq.of(), _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return EVMObj.Default();
        }
      };
    }
    StartAddress(i) {
      let _this = this;
      return (((_this).dtor_xs)[i]).StartAddress();
    };
    Size(ls) {
      let _this = this;
      let _918___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((ls).length)).isEqualTo(_dafny.ZERO)) {
          return (_dafny.ZERO).plus(_918___accumulator);
        } else {
          _918___accumulator = (_918___accumulator).plus(((ls)[_dafny.ZERO]).Size(((ls)[_dafny.ZERO]).Ins()));
          let _in116 = _this;
          let _in117 = (ls).slice(_dafny.ONE);
          _this = _in116;
          ;
          ls = _in117;
          continue TAIL_CALL_START;
        }
      }
    };
    NextG(s) {
      let _this = this;
      let _source60 = s;
      if (_source60.is_EGState) {
        let _919___mcc_h0 = (_source60).segNum;
        let _920___mcc_h1 = (_source60).st;
        let _921_st = _920___mcc_h1;
        let _922_segNum = _919___mcc_h0;
        let _923_srcSeg = ((_this).dtor_xs)[_922_segNum];
        let _924_src = State.AState.create_EState((_923_srcSeg).StartAddress(), _921_st);
        let _925_successors = _dafny.Seq.Create((_923_srcSeg).NumberOfExits(), ((_926_srcSeg, _927_src) => function (_928_i) {
          return (_926_srcSeg).Run(_927_src, _928_i, (_this).dtor_jumpDests);
        })(_923_srcSeg, _924_src));
        let _929_succGStates = MiscTypes.__default.Map(_925_successors, function (_930_s_k) {
          return function (_source61) {
            if (_source61.is_EState) {
              let _931___mcc_h3 = (_source61).pc;
              let _932___mcc_h4 = (_source61).stack;
              let _933_st = _932___mcc_h4;
              let _934_pc = _931___mcc_h3;
              if (((_this).dtor_PCToSegMap).contains(_934_pc)) {
                return CFGState.GState.create_EGState(((_this).dtor_PCToSegMap).get(_934_pc), (_930_s_k).dtor_stack);
              } else {
                return CFGState.GState.create_ErrorGState(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("NextG:  "), Int.__default.NatToString(_934_pc)), _dafny.Seq.UnicodeFromString(" not defined")));
              }
            } else {
              let _935___mcc_h5 = (_source61).msg;
              let _936_msg = _935___mcc_h5;
              return CFGState.GState.create_ErrorGState(_936_msg);
            }
          }(_930_s_k);
        });
        return _929_succGStates;
      } else {
        let _937___mcc_h2 = (_source60).msg;
        return _dafny.Seq.of();
      }
    };
    RunAll(exits, s) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((exits).length)).isEqualTo(_dafny.ZERO)) {
          return s;
        } else if (((_this).dtor_PCToSegMap).contains((s).dtor_pc)) {
          let _938_seg = ((_this).dtor_PCToSegMap).get((s).dtor_pc);
          if (((exits)[_dafny.ZERO]).isLessThan((((_this).dtor_xs)[_938_seg]).NumberOfExits())) {
            let _939_s_k = (((_this).dtor_xs)[_938_seg]).Run(s, (exits)[_dafny.ZERO], (_this).dtor_jumpDests);
            if ((_939_s_k).is_EState) {
              let _in118 = _this;
              let _in119 = (exits).slice(_dafny.ONE);
              let _in120 = _939_s_k;
              _this = _in118;
              ;
              exits = _in119;
              s = _in120;
              continue TAIL_CALL_START;
            } else {
              return State.AState.create_Error(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("Successor state of "), (s).ToString()), _dafny.Seq.UnicodeFromString(" is not an EState")));
            }
          } else {
            return State.AState.create_Error(_dafny.Seq.UnicodeFromString("Exit does not exist"));
          }
        } else {
          return State.AState.create_Error(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("No segment found for state "), (s).ToString()));
        }
      }
    };
    PreservesCond(c, exits, initpc) {
      let _this = this;
      let _pat_let_tv6 = initpc;
      let _940_initState = function (_pat_let13_0) {
        return function (_941_dt__update__tmp_h0) {
          return function (_pat_let14_0) {
            return function (_942_dt__update_hpc_h0) {
              return State.AState.create_EState(_942_dt__update_hpc_h0, (_941_dt__update__tmp_h0).dtor_stack);
            }(_pat_let14_0);
          }(_pat_let_tv6);
        }(_pat_let13_0);
      }(State.__default.BuildInitState(c, _dafny.ZERO));
      let _943_endState = (_this).RunAll(exits, _940_initState);
      if ((_943_endState).is_EState) {
        return (_943_endState).Sat(c);
      } else {
        return false;
      }
    };
    SafeLoopFound(i, pStates, pExits) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        let _source62 = (_this).FindFirstNodeWithSegIndex(i, pStates, _dafny.ZERO);
        if (_source62.is_None) {
          return MiscTypes.Option.create_None();
        } else {
          let _944___mcc_h0 = (_source62).v;
          let _945_index = _944___mcc_h0;
          let _946_pathFromIndex = (pStates).slice(_945_index);
          let _947_exitsFromIndex = (pExits).slice(_945_index);
          let _948_segmentsOnPathFromIndex = _dafny.Seq.Create(new BigNumber((_946_pathFromIndex).length), ((_949_pathFromIndex) => function (_950_i) {
            return ((_949_pathFromIndex)[_950_i]).dtor_segNum;
          })(_946_pathFromIndex));
          let _951_tgtCond = (((_this).dtor_xs)[(MiscTypes.__default.Last(pStates)).dtor_segNum]).LeadsTo((((_this).dtor_xs)[i]).StartAddress(), MiscTypes.__default.Last(pExits));
          let _952_w1 = LinSegments.__default.WPreSeqSegs(_948_segmentsOnPathFromIndex, _947_exitsFromIndex, _951_tgtCond, (_this).dtor_xs, (((_this).dtor_xs)[i]).StartAddress());
          if ((_952_w1).is_StTrue) {
            return MiscTypes.Option.create_Some(_945_index);
          } else if ((_952_w1).is_StFalse) {
            return MiscTypes.Option.create_None();
          } else if ((_this).PreservesCond(_952_w1, _947_exitsFromIndex, (((_this).dtor_xs)[i]).StartAddress())) {
            return MiscTypes.Option.create_Some(_945_index);
          } else if ((_dafny.ZERO).isLessThan(new BigNumber((_946_pathFromIndex).length))) {
            let _in121 = _this;
            let _in122 = i;
            let _in123 = (_946_pathFromIndex).slice(_dafny.ONE);
            let _in124 = (_947_exitsFromIndex).slice(_dafny.ONE);
            _this = _in121;
            ;
            i = _in122;
            pStates = _in123;
            pExits = _in124;
            continue TAIL_CALL_START;
          } else {
            return MiscTypes.Option.create_None();
          }
        }
      }
    };
    FindFirstNodeWithSegIndex(i, gs, index) {
      let _this = this;
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((gs).length)).isEqualTo(index)) {
          return MiscTypes.Option.create_None();
        } else {
          let _source63 = (gs)[index];
          if (_source63.is_EGState) {
            let _953___mcc_h0 = (_source63).segNum;
            let _954___mcc_h1 = (_source63).st;
            let _955_st = _954___mcc_h1;
            let _956_i_k = _953___mcc_h0;
            if ((_956_i_k).isEqualTo(i)) {
              return MiscTypes.Option.create_Some(index);
            } else {
              let _in125 = _this;
              let _in126 = i;
              let _in127 = gs;
              let _in128 = (index).plus(_dafny.ONE);
              _this = _in125;
              ;
              i = _in126;
              gs = _in127;
              index = _in128;
              continue TAIL_CALL_START;
            }
          } else {
            let _957___mcc_h2 = (_source63).msg;
            let _958_m = _957___mcc_h2;
            return MiscTypes.Option.create_None();
          }
        }
      }
    };
    DFS(p, a, maxDepth, debugInfo, stats) {
      let _this = this;
      let a_k = Automata.ValidAuto.Default;
      let stats_k = Statistics.Stats.Default();
      let _959_LastOnPath;
      _959_LastOnPath = MiscTypes.__default.Last((p).dtor_states);
      if (((maxDepth).isEqualTo(_dafny.ZERO)) || ((_959_LastOnPath).is_ErrorGState)) {
        let _960_stats_k;
        _960_stats_k = (((maxDepth).isEqualTo(_dafny.ZERO)) ? ((stats).SetMaxDepth()) : (stats));
        let _rhs0 = a;
        let _rhs1 = _960_stats_k;
        a_k = _rhs0;
        stats_k = _rhs1;
        return [a_k, stats_k];
      } else {
        a_k = a;
        stats_k = stats;
        let _hi4 = new BigNumber(((_this).NextG(_959_LastOnPath)).length);
        for (let _961_i = _dafny.ZERO; _961_i.isLessThan(_hi4); _961_i = _961_i.plus(_dafny.ONE)) {
          let _962_i__th__succ;
          _962_i__th__succ = ((_this).NextG(_959_LastOnPath))[_961_i];
          if ((_962_i__th__succ).is_ErrorGState) {
            let _rhs2 = (a_k).AddEdge(_959_LastOnPath, _962_i__th__succ);
            let _rhs3 = (stats_k).IncError();
            a_k = _rhs2;
            stats_k = _rhs3;
          } else if (((a_k).dtor_indexOf).contains(_962_i__th__succ)) {
            let _rhs4 = (a_k).AddEdge(_959_LastOnPath, ((a_k).dtor_states)[((a_k).dtor_indexOf).get(_962_i__th__succ)]);
            let _rhs5 = (stats_k).IncVisited();
            a_k = _rhs4;
            stats_k = _rhs5;
          } else if (!((((_this).dtor_xs)[(_959_LastOnPath).dtor_segNum]).IsJump())) {
            let _out0;
            let _out1;
            let _outcollector0 = (_this).DFS(EVMObject.Path.create_Path(_dafny.Seq.Concat((p).dtor_states, _dafny.Seq.of(_962_i__th__succ)), _dafny.Seq.Concat((p).dtor_exits, _dafny.Seq.of(_961_i))), (a_k).AddEdge(_959_LastOnPath, _962_i__th__succ), (maxDepth).minus(_dafny.ONE), debugInfo, stats_k);
            _out0 = _outcollector0[0];
            _out1 = _outcollector0[1];
            a_k = _out0;
            stats_k = _out1;
          } else {
            let _source64 = (_this).SafeLoopFound((_962_i__th__succ).dtor_segNum, (p).dtor_states, _dafny.Seq.Concat((p).dtor_exits, _dafny.Seq.of(_961_i)));
            if (_source64.is_None) {
              let _out2;
              let _out3;
              let _outcollector1 = (_this).DFS(EVMObject.Path.create_Path(_dafny.Seq.Concat((p).dtor_states, _dafny.Seq.of(_962_i__th__succ)), _dafny.Seq.Concat((p).dtor_exits, _dafny.Seq.of(_961_i))), (a_k).AddEdge(_959_LastOnPath, _962_i__th__succ), (maxDepth).minus(_dafny.ONE), debugInfo, stats_k);
              _out2 = _outcollector1[0];
              _out3 = _outcollector1[1];
              a_k = _out2;
              stats_k = _out3;
            } else {
              let _963___mcc_h0 = (_source64).v;
              let _964_index = _963___mcc_h0;
              let _rhs6 = (a_k).AddEdge(_959_LastOnPath, ((p).dtor_states)[_964_index]);
              let _rhs7 = (stats_k).IncWpre();
              a_k = _rhs6;
              stats_k = _rhs7;
            }
          }
        }
      }
      return [a_k, stats_k];
    }
    BuildCFG(maxDepth, minimise) {
      let _this = this;
      let a = Automata.ValidAuto.Default;
      let stats = Statistics.Stats.Default();
      let _965_a1;
      let _966_s1;
      let _out4;
      let _out5;
      let _outcollector2 = (_this).DFS(EVMObject.Path.create_Path(_dafny.Seq.of(CFGState.__default.DEFAULT__GSTATE), _dafny.Seq.of()), (Automata.Auto.create_Auto(_dafny.Map.Empty.slice(), _dafny.Seq.of(), _dafny.Map.Empty.slice())).AddState(CFGState.__default.DEFAULT__GSTATE), maxDepth, true, Statistics.Stats.create_Stats(false, _dafny.ZERO, _dafny.ZERO, _dafny.ZERO, _dafny.Tuple.of(_dafny.ZERO, _dafny.ZERO)));
      _out4 = _outcollector2[0];
      _out5 = _outcollector2[1];
      _965_a1 = _out4;
      _966_s1 = _out5;
      if ((!(minimise)) || (((_965_a1).SSize()).isEqualTo(_dafny.ZERO))) {
        let _rhs8 = _965_a1;
        let _rhs9 = _966_s1;
        a = _rhs8;
        stats = _rhs9;
        return [a, stats];
      } else {
        let _967_p1;
        _967_p1 = PartitionMod.__default.MakeInit((_965_a1).SSize());
        let _968_e;
        _968_e = ((_969_a1) => function (_970_x, _971_y) {
          return (((_970_x).isEqualTo(_971_y)) ? (true) : (function (_source65) {
            let _972___mcc_h0 = (_source65)[0];
            let _973___mcc_h1 = (_source65)[1];
            let _source66 = _972___mcc_h0;
            if (_source66.is_EGState) {
              let _974___mcc_h2 = (_source66).segNum;
              let _975___mcc_h3 = (_source66).st;
              let _source67 = _973___mcc_h1;
              if (_source67.is_EGState) {
                let _976___mcc_h6 = (_source67).segNum;
                let _977___mcc_h7 = (_source67).st;
                let _978_s2 = _976___mcc_h6;
                let _979_s1 = _974___mcc_h2;
                return (_979_s1).isEqualTo(_978_s2);
              } else {
                let _980___mcc_h10 = (_source67).msg;
                return false;
              }
            } else {
              let _981___mcc_h12 = (_source66).msg;
              return false;
            }
          }(_dafny.Tuple.of(((_969_a1).dtor_states)[_970_x], ((_969_a1).dtor_states)[_971_y]))));
        })(_965_a1);
        let _982_p2;
        _982_p2 = (_967_p1).ComputeFinest(_968_e);
        let _983_vp;
        _983_vp = GStateMinimiser.Pair.create_Pair(_965_a1, _982_p2);
        let _984_a2;
        _984_a2 = (_983_vp).Minimise();
        let _pat_let_tv7 = _965_a1;
        let _pat_let_tv8 = _965_a1;
        let _rhs10 = _984_a2;
        let _rhs11 = function (_pat_let15_0) {
          return function (_985_dt__update__tmp_h0) {
            return function (_pat_let16_0) {
              return function (_986_dt__update_hnonMinimisedSize_h0) {
                return Statistics.Stats.create_Stats((_985_dt__update__tmp_h0).dtor_maxDepthReached, (_985_dt__update__tmp_h0).dtor_visitedStates, (_985_dt__update__tmp_h0).dtor_wPreInvSuccess, (_985_dt__update__tmp_h0).dtor_errorState, _986_dt__update_hnonMinimisedSize_h0);
              }(_pat_let16_0);
            }(_dafny.Tuple.of((_pat_let_tv7).SSize(), (_pat_let_tv8).TSize(_dafny.ZERO)));
          }(_pat_let15_0);
        }(_966_s1);
        a = _rhs10;
        stats = _rhs11;
        return [a, stats];
      }
      return [a, stats];
    }
    ToHTML(a, withTable) {
      let _this = this;
      if ((a).is_ErrorGState) {
        return _dafny.Seq.UnicodeFromString("<ErrorEnd <BR ALIGN=\"CENTER\"/>>");
      } else if (withTable) {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<"), HTML.__default.DOTSegTable(((_this).dtor_xs)[(a).dtor_segNum], (a).dtor_segNum)), _dafny.Seq.UnicodeFromString(">"));
      } else {
        return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<"), (HTML.__default.DOTSeg(((_this).dtor_xs)[(a).dtor_segNum], (a).dtor_segNum))[0]), _dafny.Seq.UnicodeFromString(">"));
      }
    };
    DotLabel(s, exit) {
      let _this = this;
      let _987_lab = (((s).is_ErrorGState) ? (_dafny.Seq.UnicodeFromString("Error")) : (((((s).is_EGState) && ((exit).isLessThan((((_this).dtor_xs)[(s).dtor_segNum]).NumberOfExits()))) ? (((((((_this).dtor_xs)[(s).dtor_segNum]).IsJump()) && ((exit).isEqualTo(((((_this).dtor_xs)[(s).dtor_segNum]).NumberOfExits()).minus(_dafny.ONE)))) ? (_dafny.Seq.UnicodeFromString("tooltip=\"Jump\",style=dashed")) : (_dafny.Seq.UnicodeFromString("tooltip=\"Next\"")))) : (_dafny.Seq.UnicodeFromString("Error Number of exits")))));
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString(" ["), _987_lab), _dafny.Seq.UnicodeFromString("]"));
    };
    PrintByteCodeInfo() {
      let _this = this;
      let _988_listIns;
      _988_listIns = MiscTypes.__default.Flatten(MiscTypes.__default.Map((_this).dtor_xs, function (_989_s) {
        return (_989_s).Ins();
      }));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Bytecode Size: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString((_this).Size((_this).dtor_xs)));
      process.stdout.write((_dafny.Seq.UnicodeFromString(" Bytes\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Number of instructions: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((_988_listIns).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Arithmetic opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_990_i) {
        return ((_990_i).dtor_op).is_ArithOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Comparison opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_991_i) {
        return ((_991_i).dtor_op).is_CompOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Bitwise opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_992_i) {
        return ((_992_i).dtor_op).is_BitwiseOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Keccak opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_993_i) {
        return ((_993_i).dtor_op).is_KeccakOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Environmental opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_994_i) {
        return ((_994_i).dtor_op).is_EnvOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Storage opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_995_i) {
        return ((_995_i).dtor_op).is_StorageOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Memory opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_996_i) {
        return ((_996_i).dtor_op).is_MemOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Stack opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_997_i) {
        return ((_997_i).dtor_op).is_StackOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Jump opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_998_i) {
        return ((_998_i).dtor_op).is_JumpOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Log opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_999_i) {
        return ((_999_i).dtor_op).is_LogOp;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Revert/stop opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_1000_i) {
        return (((_1000_i).dtor_op).is_SysOp) && (((_1000_i).dtor_op).IsRevertStop());
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Return opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_1001_i) {
        return (((_1001_i).dtor_op).is_SysOp) && (((_1001_i).dtor_op).IsReturn());
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Invalid opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_1002_i) {
        return (((_1002_i).dtor_op).is_SysOp) && (((_1002_i).dtor_op).IsInvalid());
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("Other Systems opcodes: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter(_988_listIns, function (_1003_i) {
        return (((((_1003_i).dtor_op).is_SysOp) && (!(((_1003_i).dtor_op).IsInvalid()))) && (!(((_1003_i).dtor_op).IsRevertStop()))) && (!(((_1003_i).dtor_op).IsReturn()));
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
    PrintSegmentInfo() {
      let _this = this;
      process.stdout.write((_dafny.Seq.UnicodeFromString("Total number of segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber(((_this).dtor_xs).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of JUMP segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1004_s) {
        return (_1004_s).is_JUMPSeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of JUMPI segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1005_s) {
        return (_1005_s).is_JUMPISeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of RETURN segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1006_s) {
        return (_1006_s).is_RETURNSeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of STOP segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1007_s) {
        return (_1007_s).is_STOPSeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of CONT segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1008_s) {
        return (_1008_s).is_CONTSeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("# of INVALID segments: ")).toVerbatimString(false));
      process.stdout.write(_dafny.toString(new BigNumber((MiscTypes.__default.Filter((_this).dtor_xs, function (_1009_s) {
        return (_1009_s).is_INVALIDSeg;
      })).length)));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      return;
    }
  }
  return $module;
})(); // end of module EVMObject
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
      let _1010_cli;
      let _nw0 = new ArgParser.ArgumentParser();
      _nw0.__ctor(_dafny.Seq.UnicodeFromString("<filename>"));
      _1010_cli = _nw0;
      (_1010_cli).AddOption(_dafny.Seq.UnicodeFromString("-o"), _dafny.Seq.UnicodeFromString("--one"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("No help provided"));
      (_1010_cli).AddOption(_dafny.Seq.UnicodeFromString("-tw"), _dafny.Seq.UnicodeFromString("--two"), new BigNumber(2), _dafny.Seq.UnicodeFromString("don't do that!"));
      let _1011_r;
      _1011_r = _dafny.Seq.of(_dafny.Seq.UnicodeFromString("-one"), _dafny.Seq.UnicodeFromString("--two"), _dafny.Seq.UnicodeFromString("a1"), _dafny.Seq.UnicodeFromString("a2"), _dafny.Seq.UnicodeFromString("-unknwon"));
      let _source68 = (_1010_cli).GetArgs(_dafny.Seq.UnicodeFromString("-o"), _1011_r);
      if (_source68.is_Success) {
        let _1012___mcc_h0 = (_source68).v;
        let _1013_a = _1012___mcc_h0;
        process.stdout.write((_dafny.Seq.UnicodeFromString("Success -o! has arguments:")).toVerbatimString(false));
        process.stdout.write(_dafny.toString(_1013_a));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      } else {
        let _1014___mcc_h1 = (_source68).msg;
        let _1015_m = _1014___mcc_h1;
        process.stdout.write((_dafny.Seq.UnicodeFromString("No -o! ")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      let _source69 = (_1010_cli).GetArgs(_dafny.Seq.UnicodeFromString("--two"), _1011_r);
      if (_source69.is_Success) {
        let _1016___mcc_h2 = (_source69).v;
        let _1017_a = _1016___mcc_h2;
        process.stdout.write((_dafny.Seq.UnicodeFromString("Success -two! has arguments: ")).toVerbatimString(false));
        process.stdout.write(_dafny.toString(_1017_a));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      } else {
        let _1018___mcc_h3 = (_source69).msg;
        let _1019_m = _1018___mcc_h3;
        process.stdout.write((_dafny.Seq.UnicodeFromString("No --two! ")).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      }
      (_1010_cli).PrintHelp();
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
      let _hi5 = new BigNumber((_this.knownKeys).length);
      for (let _1020_i = _dafny.ZERO; _1020_i.isLessThan(_hi5); _1020_i = _1020_i.plus(_dafny.ONE)) {
        let _1021_k;
        _1021_k = (_this.knownArgs).get((_this.knownKeys)[_1020_i]);
        process.stdout.write((_dafny.Seq.UnicodeFromString(" [")).toVerbatimString(false));
        process.stdout.write(((_this.knownKeys)[_1020_i]).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("] ")).toVerbatimString(false));
        let _hi6 = (_1021_k).dtor_numArgs;
        for (let _1022_i = _dafny.ZERO; _1022_i.isLessThan(_hi6); _1022_i = _1022_i.plus(_dafny.ONE)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString(" arg")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(_1022_i));
        }
      }
      process.stdout.write((_dafny.Seq.UnicodeFromString(" ")).toVerbatimString(false));
      process.stdout.write((_this.usageSuffix).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n\n")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("options")).toVerbatimString(false));
      process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
      let _1023_maxL;
      _1023_maxL = (_this).MaxValueFast(_this.knownKeys, _dafny.ZERO);
      let _hi7 = new BigNumber((_this.knownKeys).length);
      for (let _1024_i = _dafny.ZERO; _1024_i.isLessThan(_hi7); _1024_i = _1024_i.plus(_dafny.ONE)) {
        let _1025_k;
        _1025_k = (_this.knownArgs).get((_this.knownKeys)[_1024_i]);
        process.stdout.write(((_this.knownKeys)[_1024_i]).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.Create(((_1023_maxL).minus(new BigNumber(((_this.knownKeys)[_1024_i]).length))).plus(new BigNumber(2)), function (_1026___v0) {
          return new _dafny.CodePoint(' '.codePointAt(0));
        })).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString(" [")).toVerbatimString(false));
        process.stdout.write(((_1025_k).dtor_name).toVerbatimString(false));
        process.stdout.write((_dafny.Seq.UnicodeFromString("] ")).toVerbatimString(false));
        process.stdout.write(((_1025_k).dtor_desc).toVerbatimString(false));
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
          let _1027_opt = (_this.knownArgs).get(key);
          let _1028_numArgs = (_1027_opt).dtor_numArgs;
          if ((new BigNumber(((s).slice(_dafny.ONE)).length)).isLessThan(_1028_numArgs)) {
            return MiscTypes.Try.create_Failure(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("argument "), (s)[_dafny.ZERO]), _dafny.Seq.UnicodeFromString(" needs more arguments")));
          } else {
            return MiscTypes.Try.create_Success(((s).slice(_dafny.ONE)).slice(0, _1028_numArgs));
          }
        } else {
          let _in129 = _this;
          let _in130 = key;
          let _in131 = (s).slice(_dafny.ONE);
          _this = _in129;
          ;
          key = _in130;
          s = _in131;
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
          let _in132 = _this;
          let _in133 = (s).slice(_dafny.ONE);
          let _in134 = Int.__default.Max(new BigNumber(((s)[_dafny.ZERO]).length), max);
          _this = _in132;
          ;
          s = _in133;
          max = _in134;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module ArgParser
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
      let _1029___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        let _pat_let_tv9 = xs;
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_1029___accumulator, _dafny.Seq.of());
        } else {
          let _1030_wpOp = ((xs)[_dafny.ZERO]).WeakestPreOperands(_dafny.ZERO);
          let _1031_wpCap = ((xs)[_dafny.ZERO]).WeakestPreCapacity(_dafny.ZERO);
          let _1032_obj = (((((xs)[_dafny.ZERO]).is_JUMPSeg) || (((xs)[_dafny.ZERO]).is_JUMPISeg)) ? (function (_pat_let17_0) {
            return function (_1033_tgt) {
              return ProofObject.ProofObj.create_JUMP((_pat_let_tv9)[_dafny.ZERO], _1030_wpOp, _1031_wpCap, _1033_tgt, _dafny.Map.Empty.slice());
            }(_pat_let17_0);
          }(SegBuilder.__default.JUMPResolver((xs)[_dafny.ZERO]))) : (((((xs)[_dafny.ZERO]).is_CONTSeg) ? (ProofObject.ProofObj.create_CONT((xs)[_dafny.ZERO], _1030_wpOp, _1031_wpCap, _dafny.Map.Empty.slice())) : (ProofObject.ProofObj.create_TERMINAL((xs)[_dafny.ZERO], _1030_wpOp, _1031_wpCap, _dafny.Map.Empty.slice())))));
          _1029___accumulator = _dafny.Seq.Concat(_1029___accumulator, _dafny.Seq.of(_1032_obj));
          let _in135 = (xs).slice(_dafny.ONE);
          xs = _in135;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module ProofObjectBuilder
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
      let _1034_optionParser;
      let _nw1 = new ArgParser.ArgumentParser();
      _nw1.__ctor(_dafny.Seq.UnicodeFromString("<string>"));
      _1034_optionParser = _nw1;
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-d"), _dafny.Seq.UnicodeFromString("--dis"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Disassemble <string>"));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-p"), _dafny.Seq.UnicodeFromString("--proof"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Generate proof object for <string>"));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-s"), _dafny.Seq.UnicodeFromString("--segment"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Print segment of <string>"));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-l"), _dafny.Seq.UnicodeFromString("--lib"), _dafny.ONE, _dafny.Seq.UnicodeFromString("The path to the Dafny-EVM source code. Used to add includes files in the proof object. "));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-c"), _dafny.Seq.UnicodeFromString("--cfg"), _dafny.ONE, _dafny.Seq.UnicodeFromString("Max depth. Control flow graph in DOT format"));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-r"), _dafny.Seq.UnicodeFromString("--raw"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Display non-minimised and minimised CFGs"));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-f"), _dafny.Seq.UnicodeFromString("--fancy"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Use exit and entry ports in segments do draw arrows."));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-n"), _dafny.Seq.UnicodeFromString("--notable"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("Don't use tables to pretty-print DOT file. Reduces size of the DOT file."));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-t"), _dafny.Seq.UnicodeFromString("--title"), _dafny.ONE, _dafny.Seq.UnicodeFromString("The name of the program."));
      (_1034_optionParser).AddOption(_dafny.Seq.UnicodeFromString("-i"), _dafny.Seq.UnicodeFromString("--info"), _dafny.ZERO, _dafny.Seq.UnicodeFromString("The stats of the program (size, segments)."));
      if (((new BigNumber((args).length)).isLessThan(new BigNumber(2))) || (_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("--help")))) {
        process.stdout.write((_dafny.Seq.UnicodeFromString("Not enough arguments\n")).toVerbatimString(false));
        (_1034_optionParser).PrintHelp();
      } else if ((new BigNumber((args).length)).isEqualTo(new BigNumber(2))) {
        if ((new BigNumber(((args)[_dafny.ONE]).length)).isEqualTo(_dafny.ZERO)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must be non empty \n")).toVerbatimString(false));
        } else if (!((new BigNumber(((args)[_dafny.ONE]).length)).mod(new BigNumber(2))).isEqualTo(_dafny.ZERO)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must be non empty and have even length, length is ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(new BigNumber(((args)[_dafny.ONE]).length)));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        } else if (Hex.__default.IsHexString(((_dafny.areEqual(((args)[_dafny.ONE]).slice(0, new BigNumber(2)), _dafny.Seq.UnicodeFromString("0x"))) ? (((args)[_dafny.ONE]).slice(new BigNumber(2))) : ((args)[_dafny.ONE])))) {
          let _1035_x;
          _1035_x = BinaryDecoder.__default.Disassemble(((_dafny.areEqual(((args)[_dafny.ONE]).slice(0, new BigNumber(2)), _dafny.Seq.UnicodeFromString("0x"))) ? (((args)[_dafny.ONE]).slice(new BigNumber(2))) : ((args)[_dafny.ONE])), _dafny.Seq.of(), _dafny.ZERO);
          process.stdout.write((_dafny.Seq.UnicodeFromString("Disassembled code:\n")).toVerbatimString(false));
          PrettyPrinters.__default.PrintInstructions(_1035_x);
          process.stdout.write((_dafny.Seq.UnicodeFromString("--------------- Disassembled ---------------------\n")).toVerbatimString(false));
        } else {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must be hexadecimal\n")).toVerbatimString(false));
        }
      } else if ((_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("--help"))) || (_dafny.areEqual((args)[_dafny.ONE], _dafny.Seq.UnicodeFromString("-h")))) {
        (_1034_optionParser).PrintHelp();
      } else {
        let _1036_stringToProcess;
        _1036_stringToProcess = (args)[(new BigNumber((args).length)).minus(_dafny.ONE)];
        if ((new BigNumber((_1036_stringToProcess).length)).isEqualTo(_dafny.ZERO)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must be non empty \n")).toVerbatimString(false));
        } else if (!((new BigNumber((_1036_stringToProcess).length)).mod(new BigNumber(2))).isEqualTo(_dafny.ZERO)) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must have even length, length is ")).toVerbatimString(false));
          process.stdout.write(_dafny.toString(new BigNumber((_1036_stringToProcess).length)));
          process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
        } else if (!(Hex.__default.IsHexString(((_dafny.areEqual((_1036_stringToProcess).slice(0, new BigNumber(2)), _dafny.Seq.UnicodeFromString("0x"))) ? ((_1036_stringToProcess).slice(new BigNumber(2))) : (_1036_stringToProcess))))) {
          process.stdout.write((_dafny.Seq.UnicodeFromString("String must be hexadecimal\n")).toVerbatimString(false));
        } else {
          let _1037_x;
          _1037_x = BinaryDecoder.__default.Disassemble(((_dafny.areEqual((_1036_stringToProcess).slice(0, new BigNumber(2)), _dafny.Seq.UnicodeFromString("0x"))) ? ((_1036_stringToProcess).slice(new BigNumber(2))) : (_1036_stringToProcess)), _dafny.Seq.of(), _dafny.ZERO);
          let _1038_optArgs;
          _1038_optArgs = (args).slice(_dafny.ONE, (new BigNumber((args).length)).minus(_dafny.ONE));
          let _1039_disOpt;
          _1039_disOpt = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--dis"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1040_segmentOpt;
          _1040_segmentOpt = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--segment"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1041_proofOpt;
          _1041_proofOpt = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--proof"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1042_libOpt;
          _1042_libOpt = function (_source70) {
            if (_source70.is_Success) {
              let _1043___mcc_h0 = (_source70).v;
              let _1044_p = _1043___mcc_h0;
              return (_1044_p)[_dafny.ZERO];
            } else {
              let _1045___mcc_h1 = (_source70).msg;
              return _dafny.Seq.UnicodeFromString("");
            }
          }((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--lib"), _1038_optArgs));
          let _1046_cfgDepthOpt;
          _1046_cfgDepthOpt = function (_source71) {
            if (_source71.is_Success) {
              let _1047___mcc_h2 = (_source71).v;
              let _1048_args = _1047___mcc_h2;
              if (((_dafny.ONE).isLessThanOrEqualTo(new BigNumber(((_1048_args)[_dafny.ZERO]).length))) && (Int.__default.IsNatNumber((_1048_args)[_dafny.ZERO]))) {
                return Int.__default.StringToNat((_1048_args)[_dafny.ZERO], _dafny.ZERO);
              } else {
                return _dafny.ZERO;
              }
            } else {
              let _1049___mcc_h3 = (_source71).msg;
              return _dafny.ZERO;
            }
          }((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--cfg"), _1038_optArgs));
          let _1050_rawOpt;
          _1050_rawOpt = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--raw"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1051_noTable;
          _1051_noTable = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--notable"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1052_info;
          _1052_info = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--info"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1053_fancy;
          _1053_fancy = ((((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--fancy"), _1038_optArgs)).is_Success) ? (true) : (false));
          let _1054_name;
          _1054_name = function (_source72) {
            if (_source72.is_Success) {
              let _1055___mcc_h4 = (_source72).v;
              let _1056_args = _1055___mcc_h4;
              return (_1056_args)[_dafny.ZERO];
            } else {
              let _1057___mcc_h5 = (_source72).msg;
              return _dafny.Seq.UnicodeFromString("Name not set");
            }
          }((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--title"), _1038_optArgs));
          if (_1039_disOpt) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("Disassembled code:\n")).toVerbatimString(false));
            PrettyPrinters.__default.PrintInstructions(_1037_x);
            process.stdout.write((_dafny.Seq.UnicodeFromString("--------------- Disassembled ---------------------\n")).toVerbatimString(false));
          }
          let _1058_y;
          _1058_y = Splitter.__default.SplitUpToTerminal(_1037_x, _dafny.Seq.of(), _dafny.Seq.of());
          let _1059_prog;
          _1059_prog = EVMObject.EVMObj.create_EVMObj(_1058_y, EVMObject.__default.CollectJumpDests(_1058_y), EVMObject.__default.CollectThem(_1058_y));
          if (_1052_info) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("-------- Program Stats ---------\n")).toVerbatimString(false));
            (_1059_prog).PrintByteCodeInfo();
            process.stdout.write((_dafny.Seq.UnicodeFromString("-------- End Program Stats ---------\n")).toVerbatimString(false));
            process.stdout.write((_dafny.Seq.UnicodeFromString("-------- Segment Stats ---------\n")).toVerbatimString(false));
            (_1059_prog).PrintSegmentInfo();
            process.stdout.write((_dafny.Seq.UnicodeFromString("-------- End Segment Stats ---------\n")).toVerbatimString(false));
          }
          if (_1040_segmentOpt) {
            process.stdout.write((_dafny.Seq.UnicodeFromString("Segments:\n")).toVerbatimString(false));
            PrettyPrinters.__default.PrintSegments(_1058_y, _dafny.ZERO);
            process.stdout.write((_dafny.Seq.UnicodeFromString("----------------- Segments -------------------\n")).toVerbatimString(false));
          }
          if (_1041_proofOpt) {
            let _1060_z;
            _1060_z = ProofObjectBuilder.__default.BuildProofObject(_1058_y);
            process.stdout.write((_dafny.Seq.UnicodeFromString("Dafny Proof Object:\n")).toVerbatimString(false));
            PrettyPrinters.__default.PrintProofObjectToDafny(_1060_z, _1042_libOpt);
            process.stdout.write((_dafny.Seq.UnicodeFromString("----------------- Proof -------------------\n")).toVerbatimString(false));
          }
          if ((((_dafny.ZERO).isLessThan(_1046_cfgDepthOpt)) && ((_dafny.ZERO).isLessThan(new BigNumber((_1058_y).length)))) && ((((_1058_y)[_dafny.ZERO]).StartAddress()).isEqualTo(_dafny.ZERO))) {
            if (_1050_rawOpt) {
              let _1061_a1;
              let _1062_s1;
              let _out6;
              let _out7;
              let _outcollector3 = (_1059_prog).BuildCFG(_1046_cfgDepthOpt, false);
              _out6 = _outcollector3[0];
              _out7 = _outcollector3[1];
              _1061_a1 = _out6;
              _1062_s1 = _out7;
              let _1063_k;
              _1063_k = MiscTypes.__default.Filter((_1061_a1).dtor_states, ((_1064_prog, _1065_a1) => function (_1066_s) {
                return (((_1066_s).is_EGState) && ((_1066_s).IsBounded(new BigNumber(((_1064_prog).dtor_xs).length)))) && ((((_1064_prog).dtor_xs)[(_1066_s).dtor_segNum]).is_INVALIDSeg);
              })(_1059_prog, _1061_a1));
              process.stdout.write((_dafny.Seq.UnicodeFromString("/*\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("maxDepth is:")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_1046_cfgDepthOpt));
              process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
              process.stdout.write(((_1062_s1).PrettyPrint()).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("# of reachable invalid segments is: ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(new BigNumber((_1063_k).length)));
              process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("Size of CFG: ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_1061_a1).SSize()));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" nodes, ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_1061_a1).TSize(_dafny.ZERO)));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" edges\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("Raw CFG\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("*/\n")).toVerbatimString(false));
              (_1061_a1).ToDot(((_1067_prog, _1068_noTable, _1069_a1) => function (_1070_s) {
                return (_1067_prog).ToHTML(_1070_s, !(_1068_noTable));
              })(_1059_prog, _1051_noTable, _1061_a1), ((_1071_prog, _1072_a1) => function (_1073_s, _1074_l, _1075___v3) {
                return (_1071_prog).DotLabel(_1073_s, _1074_l);
              })(_1059_prog, _1061_a1), _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("graph[labelloc=\"t\", labeljust=\"l\", label=<"), Driver.__default.MakeTitle(_1054_name, (_1061_a1).SSize(), (_1061_a1).TSize(_dafny.ZERO), _1046_cfgDepthOpt, (_1062_s1).dtor_maxDepthReached)), _dafny.Seq.UnicodeFromString("node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB")), _dafny.Seq.UnicodeFromString("G"));
              process.stdout.write((_dafny.Seq.UnicodeFromString("//----------------- Raw CFG -------------------\n")).toVerbatimString(false));
            } else {
              let _1076_a1;
              let _1077_s1;
              let _out8;
              let _out9;
              let _outcollector4 = (_1059_prog).BuildCFG(_1046_cfgDepthOpt, true);
              _out8 = _outcollector4[0];
              _out9 = _outcollector4[1];
              _1076_a1 = _out8;
              _1077_s1 = _out9;
              let _1078_k;
              _1078_k = MiscTypes.__default.Filter((_1076_a1).dtor_states, ((_1079_prog, _1080_a1) => function (_1081_s) {
                return (((_1081_s).is_EGState) && ((_1081_s).IsBounded(new BigNumber(((_1079_prog).dtor_xs).length)))) && ((((_1079_prog).dtor_xs)[(_1081_s).dtor_segNum]).is_INVALIDSeg);
              })(_1059_prog, _1076_a1));
              process.stdout.write((_dafny.Seq.UnicodeFromString("/*\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("maxDepth is:")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(_1046_cfgDepthOpt));
              process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
              process.stdout.write(((_1077_s1).PrettyPrint()).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("# of reachable invalid segments is: ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(new BigNumber((_1078_k).length)));
              process.stdout.write((_dafny.Seq.UnicodeFromString("\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("Size of non minimised CFG: ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(((_1077_s1).dtor_nonMinimisedSize)[0]));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" nodes, ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString(((_1077_s1).dtor_nonMinimisedSize)[1]));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" edges\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("Size of minimised CFG: ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_1076_a1).SSize()));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" nodes, ")).toVerbatimString(false));
              process.stdout.write(_dafny.toString((_1076_a1).TSize(_dafny.ZERO)));
              process.stdout.write((_dafny.Seq.UnicodeFromString(" edges\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("Minimised CFG\n")).toVerbatimString(false));
              process.stdout.write((_dafny.Seq.UnicodeFromString("*/\n")).toVerbatimString(false));
              (_1076_a1).ToDot(((_1082_prog, _1083_noTable, _1084_a1) => function (_1085_s) {
                return (_1082_prog).ToHTML(_1085_s, !(_1083_noTable));
              })(_1059_prog, _1051_noTable, _1076_a1), ((_1086_prog, _1087_a1) => function (_1088_s, _1089_l, _1090___v4) {
                return (_1086_prog).DotLabel(_1088_s, _1089_l);
              })(_1059_prog, _1076_a1), _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("graph[labelloc=\"t\", labeljust=\"l\", fontname=\"Arial\", label=<"), Driver.__default.MakeTitle(_1054_name, (_1076_a1).SSize(), (_1076_a1).TSize(_dafny.ZERO), _1046_cfgDepthOpt, (_1077_s1).dtor_maxDepthReached)), _dafny.Seq.UnicodeFromString(">]\n")), _dafny.Seq.UnicodeFromString("node [shape=none, fontname=arial, style=\"rounded, filled\", fillcolor= \"whitesmoke\"]\nedge [fontname=arial]\nranking=TB")), _dafny.Seq.UnicodeFromString("G"));
              process.stdout.write((_dafny.Seq.UnicodeFromString("//----------------- Minimised CFG -------------------\n")).toVerbatimString(false));
            }
          } else {
            if (((_1034_optionParser).GetArgs(_dafny.Seq.UnicodeFromString("--cfg"), _1038_optArgs)).is_Success) {
              process.stdout.write((_dafny.Seq.UnicodeFromString("No segment found or --cfg argument is 0 or segment 0 does not start at pc=0\n")).toVerbatimString(false));
            }
          }
        }
      }
      return;
    }
    static MakeTitle(name, numNodes, numEdges, maxDepth, reached) {
      return _dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("<B>Program Name: </B> "), name), _dafny.Seq.UnicodeFromString("<BR ALIGN=\"left\"/>")), _dafny.Seq.UnicodeFromString("<B>Control Flow Graph Info: </B><BR ALIGN=\"left\"/>")), _dafny.Seq.UnicodeFromString("Max depth: ")), Int.__default.NatToString(maxDepth)), _dafny.Seq.UnicodeFromString(" [")), ((reached) ? (_dafny.Seq.UnicodeFromString("Was reached")) : (_dafny.Seq.UnicodeFromString("Was not reached")))), _dafny.Seq.UnicodeFromString("]")), _dafny.Seq.UnicodeFromString("<BR ALIGN=\"left\"/>")), Int.__default.NatToString(numNodes)), _dafny.Seq.UnicodeFromString(" nodes/")), Int.__default.NatToString(numEdges)), _dafny.Seq.UnicodeFromString(" edges<BR ALIGN=\"left\"/>"));
    };
  };
  return $module;
})(); // end of module Driver
let _module = (function() {
  let $module = {};

  return $module;
})(); // end of module _module
_dafny.HandleHaltExceptions(() => Driver.__default.Main(_dafny.UnicodeFromMainArguments(require('process').argv)));
