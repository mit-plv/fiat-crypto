(function(a){typeof
globalThis!=="object"&&(this?b():(a.defineProperty(a.prototype,"_T_",{configurable:!0,get:b}),_T_));function
b(){var
b=this||self;b.globalThis=b;delete
a.prototype._T_}}(Object));(ag=>async a=>{"use strict";const{link:o,src:ad,generated:Q,disable_effects:N}=a,g=globalThis.process?.versions?.node,Z={cos:Math.cos,sin:Math.sin,tan:Math.tan,acos:Math.acos,asin:Math.asin,atan:Math.atan,cosh:Math.cosh,sinh:Math.sinh,tanh:Math.tanh,acosh:Math.acosh,asinh:Math.asinh,atanh:Math.atanh,cbrt:Math.cbrt,exp:Math.exp,expm1:Math.expm1,log:Math.log,log1p:Math.log1p,log2:Math.log2,log10:Math.log10,atan2:Math.atan2,hypot:Math.hypot,pow:Math.pow,fmod:(a,b)=>a%b},E=[Float32Array,Float64Array,Int8Array,Uint8Array,Int16Array,Uint16Array,Int32Array,Int32Array,Int32Array,Int32Array,Float32Array,Float64Array,Uint8Array,Uint16Array,Uint8ClampedArray],f=g&&require("node:fs"),j=new
Map(),r=new
Set(),m=new
Map();let
_=1000000;function
C(a,b){j.set(a,b);let
c=a;while(!0){const
a=c.lastIndexOf("/");if(a<=0)break;c=c.slice(0,a);r.add(c)}}if(a.files)for(const[c,b]of
Object.entries(a.files))C(c,Uint8Array.from(atob(b),a=>a.charCodeAt(0)));const
b=f?.constants,F=f?[b.R_OK,b.W_OK,b.X_OK,b.F_OK]:[],aa=f?[b.O_RDONLY,b.O_WRONLY,b.O_RDWR,b.O_APPEND,b.O_CREAT,b.O_TRUNC,b.O_EXCL,b.O_NONBLOCK,b.O_NOCTTY,b.O_DSYNC,b.O_SYNC]:[];var
h={map:new
WeakMap(),set:new
Set(),finalization:new
FinalizationRegistry(a=>h.set.delete(a))};function
ac(a){const
b=new
WeakRef(a);h.map.set(a,b);h.set.add(b);h.finalization.register(a,b,a)}function
ae(a){const
b=h.map.get(a);if(b){h.map.delete(a);h.set.delete(b);h.finalization.unregister(a)}}function
M(){return[...h.set].map(a=>a.deref()).filter(a=>a)}var
D;function
Y(a){return WebAssembly?.Suspending?new
WebAssembly.Suspending(a):a}function
A(a){return!N&&WebAssembly?.promising&&a?WebAssembly.promising(a):a}const
l=new
TextDecoder("utf-8",{ignoreBOM:1}),O=new
TextEncoder();function
n(a,b){b=Math.imul(b,0xcc9e2d51|0);b=b<<15|b>>>17;b=Math.imul(b,0x1b873593);a^=b;a=a<<13|a>>>19;return(a+(a<<2)|0)+(0xe6546b64|0)|0}function
V(a){for(var
b=0;b<a.length;b++)if(a.charCodeAt(b)>0xff)return!1;return!0}function
K(a,b){var
e=b.length,c,d;for(c=0;c+4<=e;c+=4){d=b.charCodeAt(c)|b.charCodeAt(c+1)<<8|b.charCodeAt(c+2)<<16|b.charCodeAt(c+3)<<24;a=n(a,d)}d=0;switch(e&3){case
3:d=b.charCodeAt(c+2)<<16;case
2:d|=b.charCodeAt(c+1)<<8;case
1:d|=b.charCodeAt(c);a=n(a,d)}return a^e}function
R(a,b){if(V(b))return K(a,b);var
d=b.length,c,e;for(c=0;c+2<=d;c+=2){e=b.charCodeAt(c)|b.charCodeAt(c+1)<<16;a=n(a,e)}if(d&1)a=n(a,b.charCodeAt(c));return a^d}function
z(a){if(g&&globalThis.process.env[a]!==undefined)return globalThis.process.env[a];return globalThis.jsoo_env?.[a]}let
q=0;for(const
a
of
z("OCAMLRUNPARAM")?.split(",")||[]){if(a==="b")q=1;if(a.startsWith("b="))q=+a.slice(2)?1:0}function
t(a,b){var
c;if(a.isFile())c=0;else if(a.isDirectory())c=1;else if(a.isCharacterDevice())c=2;else if(a.isBlockDevice())c=3;else if(a.isSymbolicLink())c=4;else if(a.isFIFO())c=5;else if(a.isSocket())c=6;return H(b,a.dev,a.ino|0,c,a.mode&0o7777,a.nlink,a.uid,a.gid,a.rdev,BigInt(a.size),a.atimeMs/1000,a.mtimeMs/1000,a.ctimeMs/1000)}const
B=g&&globalThis.process.platform==="win32",$=globalThis.process?.arch==="arm64",U=new
Error().stack?.includes("\n    at ")??!1,d=Function.prototype.call,c=DataView.prototype,G={jstag:WebAssembly.JSTag||new
WebAssembly.Tag({parameters:["externref"],results:[]}),identity:a=>a,from_bool:a=>!!a,get:(a,b)=>a[b],set:(a,b,c)=>a[b]=c,delete:(a,b)=>delete
a[b],instanceof:(a,b)=>a
instanceof
b,is_js_error:a=>a
instanceof
Error,to_js_string:a=>String(a),typeof:a=>typeof
a,equals:(a,b)=>a==b,strict_equals:(a,b)=>a===b,fun_call:(a,b,c)=>a.apply(b,c),meth_call:(a,b,c)=>a[b].apply(a,c),new_array:a=>new
Array(a),new_obj:()=>({}),new:(a,b)=>new
a(...b),global_this:globalThis,iter_props:(a,b)=>{for(var
c
in
a)if(Object.hasOwn(a,c))b(c)},array_length:a=>a.length,array_get:(a,b)=>a[b],array_set:(a,b,c)=>a[b]=c,read_string:a=>l.decode(new
Uint8Array(k,0,a)),read_string_stream:(a,b)=>l.decode(new
Uint8Array(k,0,a),{stream:b}),append_string:(a,b)=>a+b,write_string:a=>{var
c=0,b=a.length;for(;;){const{read:d,written:e}=O.encodeInto(a.slice(c),ab);b-=d;if(!b)return e;J(e);c+=d}},ta_create:(a,b)=>new
E[a](b),ta_normalize:a=>a
instanceof
Uint32Array?new
Int32Array(a.buffer,a.byteOffset,a.length):a,ta_kind:b=>E.findIndex(a=>b
instanceof
a),ta_length:a=>a.length,ta_get_i32:(a,b)=>a[b],ta_fill:(a,b)=>a.fill(b),ta_blit:(a,b)=>b.set(a),ta_subarray:(a,b,c)=>a.subarray(b,c),ta_set:(a,b,c)=>a.set(b,c),ta_new:a=>new
Uint8Array(a),ta_copy:(a,b,c,d)=>a.copyWithin(b,c,d),ta_bytes:a=>new
Uint8Array(a.buffer,a.byteOffset,a.length*a.BYTES_PER_ELEMENT),dv_make:a=>new
DataView(a.buffer,a.byteOffset,a.byteLength),dv_get_f64:d.bind(c.getFloat64),dv_get_f32:d.bind(c.getFloat32),dv_get_i64:d.bind(c.getBigInt64),dv_get_i32:U?d.bind(c.getInt32):(a,b,c)=>a.getInt32(b,c),dv_get_i16:d.bind(c.getInt16),dv_get_ui16:d.bind(c.getUint16),dv_get_i8:d.bind(c.getInt8),dv_get_ui8:d.bind(c.getUint8),dv_set_f64:d.bind(c.setFloat64),dv_set_f32:d.bind(c.setFloat32),dv_set_i64:d.bind(c.setBigInt64),dv_set_i32:d.bind(c.setInt32),dv_set_i16:d.bind(c.setInt16),dv_set_i8:d.bind(c.setInt8),littleEndian:new
Uint8Array(new
Uint32Array([1]).buffer)[0],wrap_callback:b=>function(...a){if(a.length===0)a=[undefined];return i(b,a.length,a,1)},wrap_callback_args:b=>function(...a){return i(b,1,[a],0)},wrap_callback_strict:(c,b)=>function(...a){a.length=c;return i(b,c,a,0)},wrap_callback_unsafe:b=>function(...a){return i(b,a.length,a,2)},wrap_meth_callback:b=>function(...a){a.unshift(this);return i(b,a.length,a,1)},wrap_meth_callback_args:b=>function(...a){return i(b,2,[this,a],0)},wrap_meth_callback_strict:(c,b)=>function(...a){a.length=c;a.unshift(this);return i(b,a.length,a,0)},wrap_meth_callback_unsafe:b=>function(...a){a.unshift(this);return i(b,a.length,a,2)},wrap_fun_arguments:b=>function(...a){return b(a)},format_float:(a,b,c,d)=>{function
m(a){var
b=new
DataView(new
ArrayBuffer(8));b.setFloat64(0,a);var
d=b.getUint32(0),f=b.getUint32(4),c=d>>>20&0x7ff,e=BigInt(d&0xfffff)<<32n|BigInt(f);if(c===0)return[e,-1074];return[e|1n<<52n,c-1075]}function
k(a,b){var
d=m(a),e=d[0],c=1n;if(b>=0)e*=10n**BigInt(b);else
c=10n**BigInt(-b);if(d[1]>=0)e<<=BigInt(d[1]);else
c<<=BigInt(-d[1]);var
f=e/c,g=e%c*2n;if(g>c||g===c&&f&1n)f+=1n;return f}function
o(a,b){var
c=k(a,b).toString();if(b===0)return c;if(c.length<=b)c="0".repeat(b+1-c.length)+c;return c.slice(0,c.length-b)+"."+c.slice(c.length-b)}function
n(a,b){if(a===0)return(b>0?"0."+"0".repeat(b):"0")+"e+0";var
d=Math.floor(Math.log10(a));for(;;){var
c=k(a,b-d).toString();if(c.length===b+1){var
e=b>0?c.charAt(0)+"."+c.slice(1):c;return e+"e"+(d<0?"-":"+")+Math.abs(d)}d+=c.length-(b+1)}}function
l(a,b){return b>100?n(a,b):a.toExponential(b)}function
j(a,b){if(b>100||a>=1e21)return o(a,b);return a.toFixed(b)}switch(b){case
0:var
e=l(d,a),f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break;case
1:e=j(d,a);break;case
2:a=a?a:1;e=l(d,a-1);var
i=e.indexOf("e"),h=+e.slice(i+1);if(h<-4||d>=1e21||d.toFixed(0).length>a){var
f=i-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)+e.slice(i);f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break}else{var
g=a;if(h<0){g-=h+1;e=j(d,g)}else
while(e=j(d,g),e.length>a+1)g--;if(g){var
f=e.length-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)}}break}return c?" "+e:e},gettimeofday:()=>Date.now()/1000,times:()=>{if(globalThis.process?.cpuUsage){var
a=globalThis.process.cpuUsage();return v(a.user/1e6,a.system/1e6)}else{var
a=performance.now()/1000;return v(a,0)}},gmtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),e=new
Date(Date.UTC(b.getUTCFullYear(),0,1)).getTime(),d=Math.floor((c-e)/86400000);return w(b.getUTCSeconds(),b.getUTCMinutes(),b.getUTCHours(),b.getUTCDate(),b.getUTCMonth(),b.getUTCFullYear()-1900,b.getUTCDay(),d,!1)},localtime:a=>{var
b=new
Date(a*1000),g=Math.floor((Date.UTC(b.getFullYear(),b.getMonth(),b.getDate())-Date.UTC(b.getFullYear(),0,1))/86400000),d=new
Date(b.getFullYear(),0,1),e=new
Date(b.getFullYear(),6,1),f=Math.max(d.getTimezoneOffset(),e.getTimezoneOffset()),c=b.getTimezoneOffset()<f;if(f===0&&d.getTimezoneOffset()!==e.getTimezoneOffset()&&globalThis.Intl?.DateTimeFormat?.().resolvedOptions().timeZone==="Europe/Dublin")c=!c;return w(b.getSeconds(),b.getMinutes(),b.getHours(),b.getDate(),b.getMonth(),b.getFullYear()-1900,b.getDay(),g,c)},mktime:(a,b,c,d,e,f)=>new
Date(a,b,c,d,e,f).getTime(),random_seed:()=>crypto.getRandomValues(new
Int32Array(12)),access:(a,d)=>f.accessSync(a,F.reduce((a,b,c)=>d&1<<c?a|b:a,0)),open:(a,d,c)=>{if(j.has(a)&&!(d&2)){const
b=_++;m.set(b,{data:j.get(a),offset:0});return b}return f.openSync(a,aa.reduce((a,b,c)=>d&1<<c?a|b:a,0),c)},close:a=>{if(m.has(a)){m.delete(a);return}f.closeSync(a)},write:(a,b,c,d,e)=>f?f.writeSync(a,b,c,d,e===null?e:Number(e)):(console[a===2?"error":"log"](typeof
b==="string"?b:l.decode(b.slice(c,c+d))),d),read:(a,b,c,d,e)=>{const
g=m.get(a);if(g){const
f=e===null?g.offset:Number(e),a=Math.min(d,g.data.length-f);if(a<=0)return 0;b.set(g.data.subarray(f,f+a),c);g.offset=f+a;return a}return f.readSync(a,b,c,d,e)},fsync:a=>f.fsyncSync(a),file_size:a=>{const
b=m.get(a);if(b)return BigInt(b.data.length);return f.fstatSync(a,{bigint:!0}).size},register_channel:ac,unregister_channel:ae,channel_list:M,exit:a=>g&&globalThis.process.exit(a),argv:()=>g?globalThis.process.argv.slice(1):["a.out"],on_windows:+B,on_arm64:+$,getenv:z,backtrace_status:()=>q,record_backtrace:a=>q=a,system:a=>{var
b=require("node:child_process").spawnSync(a,{shell:!0,stdio:"inherit"});if(b.error)throw b.error;return b.signal?255:b.status},isatty:a=>g?+require("node:tty").isatty(a):0,getuid:()=>globalThis.process?.getuid?globalThis.process.getuid():1,geteuid:()=>globalThis.process?.geteuid?globalThis.process.geteuid():1,getgid:()=>globalThis.process?.getgid?globalThis.process.getgid():1,getegid:()=>globalThis.process?.getegid?globalThis.process.getegid():1,time:()=>performance.now(),getcwd:()=>g?globalThis.process.cwd():"/static",chdir:a=>globalThis.process.chdir(a),mkdir:(a,b)=>f.mkdirSync(a,b),rmdir:a=>f.rmdirSync(a),link:(a,b)=>f.linkSync(a,b),symlink:(a,b,c)=>f.symlinkSync(a,b,[null,"file","dir"][c]),readlink:a=>f.readlinkSync(a),unlink:a=>f.unlinkSync(a),read_dir:a=>{const
c=a.endsWith("/")?a:a+"/",b=new
Set();for(const
d
of
j.keys())if(d.startsWith(c)){const
a=d.slice(c.length),e=a.indexOf("/");b.add(e<0?a:a.slice(0,e))}if(f)try{for(const
c
of
f.readdirSync(a))b.add(c)}catch(f){if(b.size===0)throw f}return[...b]},opendir:a=>({dir:f.opendirSync(a),dots:[".",".."]}),readdir:a=>{if(a.dots.length>0)return a.dots.shift();var
b=a.dir.readSync()?.name;return b===undefined?null:b},closedir:a=>{a.dots=[];a.dir.closeSync()},stat:(a,b)=>t(f.statSync(a),b),lstat:(a,b)=>t(f.lstatSync(a),b),fstat:(a,b)=>t(f.fstatSync(a),b),chmod:(a,b)=>f.chmodSync(a,b),fchmod:(a,b)=>f.fchmodSync(a,b),file_exists:a=>{if(j.has(a)||r.has(a))return 1;return f?+f.existsSync(a):0},is_directory:a=>{if(r.has(a))return 1;if(j.has(a))return 0;return+f.statSync(a).isDirectory()},is_file:a=>{if(j.has(a))return 1;if(r.has(a))return 0;return+f.statSync(a).isFile()},utimes:(a,b,c)=>f.utimesSync(a,b,c),truncate:(a,b)=>f.truncateSync(a,b),ftruncate:(a,b)=>f.ftruncateSync(a,b),rename:(a,b)=>{var
c;if(B&&(c=f.statSync(b,{throwIfNoEntry:!1}))&&f.statSync(a,{throwIfNoEntry:!1})?.isDirectory())if(c.isDirectory()){if(!b.startsWith(a))try{f.rmdirSync(b)}catch{}}else{var
d=new
Error(`ENOTDIR: not a directory, rename '${a}' -> '${b}'`);throw Object.assign(d,{errno:-20,code:"ENOTDIR",syscall:"rename",path:b})}f.renameSync(a,b)},tmpdir:()=>require("node:os").tmpdir(),start_fiber:a=>D(a),suspend_fiber:Y((c,b)=>new
Promise(a=>c(a,b))),resume_fiber:(a,b)=>a(b),weak_new:a=>new
WeakRef(a),weak_deref:a=>{var
b=a.deref();return b===undefined?null:b},weak_map_new:()=>new
WeakMap(),map_new:()=>new
Map(),map_get:(a,b)=>{var
c=a.get(b);return c===undefined?null:c},map_set:(a,b,c)=>a.set(b,c),map_delete:(a,b)=>a.delete(b),hash_string:R,log:a=>console.log(a),register_fragments:(a,b)=>{const
c=eval?.(b);e[a+".fragments"]=c},load_module:a=>{const
c=new
WebAssembly.Module(a,p),b=new
WebAssembly.Instance(c,e);Object.assign(e.OCaml,b.exports);return b.exports["_dynlink.init"]()},load_wasmo:a=>{const
b=new
DataView(a.buffer,a.byteOffset,a.byteLength),j=a.byteLength;let
d=j-22;while(d>=0&&b.getUint32(d,!0)!==0x06054b50)d--;if(d<0)throw new
Error("Invalid ZIP: EOCD not found");const
i=b.getUint32(d+16,!0),h=b.getUint16(d+10,!0),f={};let
c=i;for(let
d=0;d<h;d++){if(b.getUint32(c,!0)!==0x02014b50)throw new
Error("Invalid ZIP: bad CD entry");const
g=b.getUint16(c+28,!0),i=b.getUint16(c+30,!0),h=b.getUint16(c+32,!0),d=b.getUint32(c+42,!0),m=l.decode(a.subarray(c+46,c+46+g)),n=b.getUint32(c+24,!0),k=b.getUint16(d+26,!0),j=b.getUint16(d+28,!0),e=d+30+k+j;f[m]=a.subarray(e,e+n);c+=46+g+i+h}if(!f["code.wasm"])throw new
Error("code.wasm not found in .wasmo");const
k=new
WebAssembly.Module(f["code.wasm"],p),g=new
WebAssembly.Instance(k,e);Object.assign(e.OCaml,g.exports);const
m=l.decode(f.link_order).split("\x00");for(const
a
of
m)g.exports[a+".init"]()},register_file:(a,b)=>C(a,b),read_file:a=>j.get(a)??null},u={test:a=>+(typeof
a==="string"),compare:(a,b)=>a<b?-1:+(a>b),decodeStringFromUTF8Array:()=>"",encodeStringToUTF8Array:()=>0,fromCharCodeArray:()=>"",length:a=>a.length,intoCharCodeArray:()=>0},e=Object.assign({Math:Z,bindings:G,js:ag,"wasm:js-string":u,"wasm:text-decoder":u,"wasm:text-encoder":u,str:new
globalThis.Proxy({},{get(a,b){return b}}),env:{}},Q),p={builtins:["js-string","text-decoder","text-encoder"],importedStringConstants:"str"};function
X(a){const
b=require("node:path"),c=b.join(b.dirname(require.main.filename),a);return require("node:fs/promises").readFile(c)}const
y=globalThis?.document?.currentScript?.src;function
P(a){const
b=y?new
URL(a,y):a;return fetch(b)}const
W=g?X:P;async function
T(a){return g?WebAssembly.instantiate(await
a,e,p):WebAssembly.instantiateStreaming(a,e,p)}async function
S(){e.OCaml={};const
c=[];async function
b(a,b){const
g=a[1].constructor!==Array;async function
f(){const
d=W(ad+"/"+a[0]+".wasm");await
Promise.all(g?c:a[1].map(a=>c[a]));const
f=await
T(d);Object.assign(b?e.env:e.OCaml,f.instance.exports)}const
d=f();c.push(d);return d}async function
a(a){for(const
c
of
a)await
b(c)}await
b(o[0],1);if(o.length>1){await
b(o[1]);const
c=new
Array(20).fill(o.slice(2).values()).map(a);await
Promise.all(c)}return{instance:{exports:Object.assign(e.env,e.OCaml)}}}const
af=await
S();var{caml_callback:i,caml_alloc_times:v,caml_alloc_tm:w,caml_alloc_stat:H,caml_start_fiber:L,caml_handle_uncaught_exception:x,caml_buffer:I,caml_extract_bytes:J,_initialize:s}=af.instance.exports,k=I?.buffer,ab=k&&new
Uint8Array(k,0,k.length);D=A(L);var
s=A(s);if(globalThis.process?.on)globalThis.process.on("uncaughtException",(a,b)=>x(a));else if(globalThis.addEventListener)globalThis.addEventListener("error",a=>a.error&&x(a.error));await
s()})(function(a){"use strict";return{}}(globalThis))({"link":[["code-788b974394cb05968065",0]],"generated":(a=>{var
c=a,b=a?.module?.export||a;return{"fragments":{"get_Array":a=>a.Array,"get_Date":a=>a.Date,"get_Error":a=>a.Error,"get_JSON":a=>a.JSON,"get_Math":a=>a.Math,"get_Object":a=>a.Object,"get_RegExp":a=>a.RegExp,"get_String":a=>a.String,"get_length":a=>a.length,"js_expr_12c48ca8":()=>a,"js_expr_21711c2a":()=>b,"meth_call_0_toString":a=>a.toString()}}})(globalThis),"src":"fiat_crypto.assets"});
