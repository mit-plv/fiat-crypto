This folder contains JSON representations of the files.  The format is
a bit ad-hoc; here is a partial description:

The types of the fields:

Let `string` be the standard string type, let `[t]` stand for an array
whose elements have type `t`, let `t | u` denote the union of types
`t` and `u`.  String literals will be used as singleton types
containing only themselves, and we will use braces (`{` and `}`) for
standard JSON objects/dictionaries.

Let us define the following types:

- `datatype`, which is either the literal `"(auto)"`, a string
  matching the regex `/(u|i)\d+/`, standing for an unsigned (u) or
  signed (i) integer of a given number of bits, or a string matching
  the regex `/(u|i)\d+\[\d+\]/`, standing for an array of the given
  length of the given integer type

- `varname`, either the literal `"_"` (for unused variables) or a
  string matching `/x\d+/`

- `name`, which is either `varname`, a string matching
  `/(arg|out)\d+\[\d+\]/` for input/output arrays, the literal `&`
  followed by a `varname` (for references), or the literal `*`
  followed by a `varname` for dereferences.  These last two are very
  rare, and we make an effort to avoid them in code generation.

- `operation`, a string which is one of `=`, `dereference`, `>>`,
  `<<`, `&` (infix bitwise and), `|` (infix bitwise or), `~` (bitwise
  negation), `!` (boolean negation), `+`, `*`, `-`, `mulx`,
  `addcarryx`, `subborrowx`, `cmovznz`, or `static_cast`

- `number`, a string which is either a decimal numeral or a
  hexadecimal numeral

- `bound`, either `null` or a `number` or a list of `bound`s

- `parameters`, a JSON object with `string` keys and `string | number` values

Let us define one more type.  The recursive type of expressions
(corresponding to lines of code or expressions) `expr` has the format:

```json
{
"datatype"  : datatype,
"name"      : [name],
"operation" : operation,
"parameters": parameters
"arguments" : [ name | expr | number ]
}
```

When `parameters` is empty, the entire `"parameters": { parameters }`
key-value pair will be omitted.

It describes a line of code or an expression:

- whose output type is specified by `"datatype"` (`"(auto)"` means
  that the type should be inferred automatically, and is generally
  used only in assignment statements),

- whose output(s) are stored in the variables in `"name"` (an empty
  list means that the value is used immediately in the enclosing
  expression),

- whose kind of function / operation is given by the `"operation"`
  field,

- whose compile-time constant parameters are given by the
  `"parameters"` field (currently only relevant for `mulx`,
  `addcarryx`, and `subborrowx`, all of which have a single parameter
  `"size"` which is an integer bitwidth denoting the carry location),
  and

- whose arguments are the in the arguments field, which may be either
  subexpressions or variable names

The format of top-level functions is:

```json
{
"operation": string,
"arguments": [{"datatype": datatype, "name": varname, "lbound": bound, "ubound": bound}],
"returns": [{"datatype": datatype, "name": varname, "lbound": bound, "ubound": bound}],
"body": [expr]
}
```

Note that here `"operation"` is just the name of the function, and may
be something like `fiat_25519_carry_mul`.

The fields `"lbound"` and `"ubound"` stand for "lower bound" and
"upper bound" respectively.  The bounds are assumptions about the
arguments, and guarantees about the returns.  If the `"datatype"` is
an integer, the bounds will either be `null` or a string with a
hexadecimal number.  If the `"datatype"` is a list of integers, the
bounds will either be `null` or a list of the appropriate length
containing either `null` or strings with hexadecimal encodings of
numbers.  Bounds of `null` should never appear, and indicate that
bounds were either not given, unknown, or that the bounds analysis
pass failed.

Note that errors in the pretty-printing process may be encoded with
`#error ...`; these can be detected by running the code through a JSON
validator, as the resulting code will not be valid JSON.


-----------------------


Here a few examples:

`uint64_t x1 = (arg1[1]);` corresponds to a JSON-Object such as:
```json
{
"datatype": "u64",
"name": ["x1"],
"operation": "=",
"arguments": ["arg1[1]"]
}
```


```c
fiat_p256_mulx_u64(&x5, &x6, x4, (arg1[3]));
```
would correspond to:
```json
{
"datatype": "(auto)",
"name": ["x5", "x6"],
"operation": "mulx",
"parameters": {"size": 64},
"arguments": ["x4", "arg1[3]"]
}
```
from the combination `"mulx"` and `"size": 64` we can infer, which elements from
the name-property is high/low limb.

```c
fiat_p256_subborrowx_u64(&x180, &x181, x179, x171, UINT64_C(0xffffffff00000001));
```
would correspond to
```json
{
"datatype": "(auto)",
"name": ["x180", "x181"],
"operation": "subborrowx",
"parameters": {"size": 64},
"arguments": ["x179", "x171", "0xffffffff00000001"]
}
```
also, we can infer from `subborrowx` which arguments have which meaning
and which variable in `"name"` contains the carry out.

```c
fiat_p256_addcarryx_u51(&x180, &x181, x179, x171, UINT64_C(0xffffffff00000001));
```
would correspond to
```json
{
"datatype": "(auto)",
"name": ["x180", "x181"],
"operation": "addcarryx",
"parameters": {"size": 51},
"arguments": ["x179", "x171", "0xffffffff00000001"]
}
```

```c
uint64_t x173 = ((uint64_t)x172 + x153);
```
```json
{
"datatype": "u64",
"name": ["x173"],
"operation": "+",
"arguments": ["x172", "x153"]
}
```

```c
fiat_p256_cmovznz_u64(&x184, x183, x174, x165);
```
```json
{
"datatype": "u64",
"name": ["x184"],
"operation": "cmovznz",
"arguments": ["x183", "x174", "x165"]
}
```
`cmovznz` means semantically `names[0] = arguments[0] == 0 ? arguments[1] :
arguments[2]`, or replaced: `x184 <- x183 == 0 ? x174 : x165`;


```c
fiat_25519_uint128 x14 = ((fiat_25519_uint128)(arg1[2]) * (arg1[1]));
```
```json
{
"datatype": "u128",
"name": ["x14"],
"operation": "*",
"arguments": ["arg1[2]", "arg1[1]"]
}
```

```c
uint64_t x45 = (x44 >> 51);
```
```json
{
"datatype": "u64",
"name": ["x45"],
"operation": ">>",
"arguments": ["x44", "51"]
}
```
Note that, at least currently, `arguments[1]` will always be an immediate
value

```c
fiat_25519_uint1 x48 = (fiat_25519_uint1)(x47 >> 51);
```
```json
{
"datatype": "u1",
"name": ["x48"],
"operation": ">>",
"arguments": ["x47", "51"]
}
```

```c
uint64_t x105 = (x92 + (x83 + (x75 + (x68 + (x62 + (x57 + (x53 + (x50 + (x48 + x1)))))))));
```
```json
{
 "datatype": "u64",
 "name": ["x105"],
 "operation": "+",
 "arguments": [
  "x92"
  ,
  {
   "datatype": "u64",
   "name": [],
   "operation": "+",
   "arguments": [
    "x83"
    ,
    {
     "datatype": "u64",
     "name": [],
     "operation": "+",
     "arguments": [
      "x75"
      ,
      {
       "datatype": "u64",
       "name": [],
       "operation": "+",
       "arguments": [
        "x68"
        ,
        {
         "datatype": "u64",
         "name": [],
         "operation": "+",
         "arguments": [
          "x62"
          ,
          {
           "datatype": "u64",
           "name": [],
           "operation": "+",
           "arguments": [
            "x57"
            ,
            {
             "datatype": "u64",
             "name": [],
             "operation": "+",
             "arguments": [
              "x53"
              ,
              {
               "datatype": "u64",
               "name": [],
               "operation": "+",
               "arguments": [
                "x50"
                ,
                {
                 "datatype": "u64",
                 "name": [],
                 "operation": "+",
                 "arguments": [
                  "x48"
                  ,
                  "x1"
                 ]
                }
               ]
              }
             ]
            }
           ]
          }
         ]
        }
       ]
      }
     ]
    }
   ]
  }
 ]
}
```
