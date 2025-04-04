(function(a){typeof
globalThis!=="object"&&(this?b():(a.defineProperty(a.prototype,"_T_",{configurable:true,get:b}),_T_));function
b(){var
b=this||self;b.globalThis=b;delete
a.prototype._T_}}(Object));
(v=>async a=>{"use strict";const{link:i,src:Q,generated:E}=a,e=globalThis?.process?.versions?.node,M={cos:Math.cos,sin:Math.sin,tan:Math.tan,acos:Math.acos,asin:Math.asin,atan:Math.atan,cosh:Math.cosh,sinh:Math.sinh,tanh:Math.tanh,acosh:Math.acosh,asinh:Math.asinh,atanh:Math.atanh,cbrt:Math.cbrt,exp:Math.exp,expm1:Math.expm1,log:Math.log,log1p:Math.log1p,log2:Math.log2,log10:Math.log10,atan2:Math.atan2,hypot:Math.hypot,pow:Math.pow,fmod:(a,b)=>a%b},u=[Float32Array,Float64Array,Int8Array,Uint8Array,Int16Array,Uint16Array,Int32Array,Int32Array,Int32Array,Int32Array,Float32Array,Float64Array,Uint8Array,Uint16Array,Uint8ClampedArray],f=e&&require("node:fs"),b=f?.constants,N=f?[b.O_RDONLY,b.O_WRONLY,b.O_RDWR,b.O_APPEND,b.O_CREAT,b.O_TRUNC,b.O_EXCL,b.O_NONBLOCK,b.O_NOCTTY,b.O_DSYNC,b.O_SYNC]:[];var
c={map:new
WeakMap(),set:new
Set(),finalization:new
FinalizationRegistry(a=>c.set.delete(a))};function
P(a){const
b=new
WeakRef(a);c.map.set(a,b);c.set.add(b);c.finalization.register(a,b,a)}function
T(a){const
b=c.map.get(a);if(b){c.map.delete(a);c.set.delete(b);c.finalization.unregister(a)}}function
B(){return[...c.set].map(a=>a.deref()).filter(a=>a)}var
t;function
L(a){return WebAssembly?.Suspending?new
WebAssembly.Suspending(a):a}function
q(a){return WebAssembly?.promising&&a?WebAssembly.promising(a):a}const
l=new
TextDecoder("utf-8",{ignoreBOM:1}),C=new
TextEncoder();function
F(a,b){b=Math.imul(b,0xcc9e2d51|0);b=b<<15|b>>>17;b=Math.imul(b,0x1b873593);a^=b;a=a<<13|a>>>19;return(a+(a<<2)|0)+(0xe6546b64|0)|0}function
G(a,b){for(var
c=0;c<b.length;c++)a=F(a,b.charCodeAt(c));return a^b.length}function
k(a,b){var
c;if(a.isFile())c=0;else if(a.isDirectory())c=1;else if(a.isCharacterDevice())c=2;else if(a.isBlockDevice())c=3;else if(a.isSymbolicLink())c=4;else if(a.isFIFO())c=5;else if(a.isSocket())c=6;return x(b,a.dev,a.ino|0,c,a.mode,a.nlink,a.uid,a.gid,a.rdev,BigInt(a.size),a.atimeMs/1000,a.mtimeMs/1000,a.ctimeMs/1000)}const
r=e&&process.platform==="win32",w={jstag:WebAssembly.JSTag||new
WebAssembly.Tag({parameters:["externref"],results:[]}),identity:a=>a,from_bool:a=>!!a,get:(a,b)=>a[b],set:(a,b,c)=>a[b]=c,delete:(a,b)=>delete
a[b],instanceof:(a,b)=>a
instanceof
b,typeof:a=>typeof
a,equals:(a,b)=>a==b,strict_equals:(a,b)=>a===b,fun_call:(a,b,c)=>a.apply(b,c),meth_call:(a,b,c)=>a[b].apply(a,c),new_array:a=>new
Array(a),new_obj:()=>({}),new:(a,b)=>new
a(...b),global_this:globalThis,iter_props:(a,b)=>{for(var
c
in
a)if(Object.hasOwn(a,c))b(c)},array_length:a=>a.length,array_get:(a,b)=>a[b],array_set:(a,b,c)=>a[b]=c,read_string:a=>l.decode(new
Uint8Array(h,0,a)),read_string_stream:(a,b)=>l.decode(new
Uint8Array(h,0,a),{stream:b}),append_string:(a,b)=>a+b,write_string:a=>{var
c=0,b=a.length;for(;;){const{read:d,written:e}=C.encodeInto(a.slice(c),O);b-=d;if(!b)return e;z(e);c+=d}},ta_create:(a,b)=>new
u[a](b),ta_normalize:a=>a
instanceof
Uint32Array?new
Int32Array(a.buffer,a.byteOffset,a.length):a,ta_kind:b=>u.findIndex(a=>b
instanceof
a),ta_length:a=>a.length,ta_get_f64:(a,b)=>a[b],ta_get_f32:(a,b)=>a[b],ta_get_i32:(a,b)=>a[b],ta_get_i16:(a,b)=>a[b],ta_get_ui16:(a,b)=>a[b],ta_get_i8:(a,b)=>a[b],ta_get_ui8:(a,b)=>a[b],ta_get16_ui8:(a,b)=>a[b]|a[b+1]<<8,ta_get32_ui8:(a,b)=>a[b]|a[b+1]<<8|a[b+2]<<16|a[b+3]<<24,ta_set_f64:(a,b,c)=>a[b]=c,ta_set_f32:(a,b,c)=>a[b]=c,ta_set_i32:(a,b,c)=>a[b]=c,ta_set_i16:(a,b,c)=>a[b]=c,ta_set_ui16:(a,b,c)=>a[b]=c,ta_set_i8:(a,b,c)=>a[b]=c,ta_set_ui8:(a,b,c)=>a[b]=c,ta_set16_ui8:(a,b,c)=>{a[b]=c;a[b+1]=c>>8},ta_set32_ui8:(a,b,c)=>{a[b]=c;a[b+1]=c>>8;a[b+2]=c>>16;a[b+3]=c>>24},ta_fill:(a,b)=>a.fill(b),ta_blit:(a,b)=>b.set(a),ta_subarray:(a,b,c)=>a.subarray(b,c),ta_set:(a,b,c)=>a.set(b,c),ta_new:a=>new
Uint8Array(a),ta_copy:(a,b,c,d)=>a.copyWithin(b,c,d),ta_bytes:a=>new
Uint8Array(a.buffer,a.byteOffset,a.length*a.BYTES_PER_ELEMENT),ta_blit_from_string:(a,b,c,d,e)=>{for(let
f=0;f<e;f++)c[d+f]=R(a,b+f)},ta_blit_to_string:(a,b,c,d,e)=>{for(let
f=0;f<e;f++)S(c,d+f,a[b+f])},wrap_callback:b=>function(...a){if(a.length===0)a=[undefined];return d(b,a.length,a,1)},wrap_callback_args:b=>function(...a){return d(b,1,[a],0)},wrap_callback_strict:(c,b)=>function(...a){a.length=c;return d(b,c,a,0)},wrap_callback_unsafe:b=>function(...a){return d(b,a.length,a,2)},wrap_meth_callback:b=>function(...a){a.unshift(this);return d(b,a.length,a,1)},wrap_meth_callback_args:b=>function(...a){return d(b,2,[this,a],0)},wrap_meth_callback_strict:(c,b)=>function(...a){a.length=c;a.unshift(this);return d(b,a.length,a,0)},wrap_meth_callback_unsafe:b=>function(...a){a.unshift(this);return d(b,a.length,a,2)},wrap_fun_arguments:b=>function(...a){return b(a)},format_float:(a,b,c,d)=>{function
j(a,b){if(Math.abs(a)<1.0)return a.toFixed(b);else{var
c=Number.parseInt(a.toString().split("+")[1]);if(c>20){c-=20;a/=Math.pow(10,c);a+=new
Array(c+1).join("0");if(b>0)a=a+"."+new
Array(b+1).join("0");return a}else
return a.toFixed(b)}}switch(b){case
0:var
e=d.toExponential(a),f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break;case
1:e=j(d,a);break;case
2:a=a?a:1;e=d.toExponential(a-1);var
i=e.indexOf("e"),h=+e.slice(i+1);if(h<-4||d>=1e21||d.toFixed(0).length>a){var
f=i-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)+e.slice(i);f=e.length;if(e.charAt(f-3)==="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break}else{var
g=a;if(h<0){g-=h+1;e=d.toFixed(g)}else
while(e=d.toFixed(g),e.length>a+1)g--;if(g){var
f=e.length-1;while(e.charAt(f)==="0")f--;if(e.charAt(f)===".")f--;e=e.slice(0,f+1)}}break}return c?" "+e:e},gettimeofday:()=>new
Date().getTime()/1000,gmtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),e=new
Date(Date.UTC(b.getUTCFullYear(),0,1)).getTime(),d=Math.floor((c-e)/86400000);return n(b.getUTCSeconds(),b.getUTCMinutes(),b.getUTCHours(),b.getUTCDate(),b.getUTCMonth(),b.getUTCFullYear()-1900,b.getUTCDay(),d,false)},localtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),f=new
Date(b.getFullYear(),0,1).getTime(),d=Math.floor((c-f)/86400000),e=new
Date(b.getFullYear(),0,1),g=new
Date(b.getFullYear(),6,1),h=Math.max(e.getTimezoneOffset(),g.getTimezoneOffset());return n(b.getSeconds(),b.getMinutes(),b.getHours(),b.getDate(),b.getMonth(),b.getFullYear()-1900,b.getDay(),d,b.getTimezoneOffset()<h)},mktime:(a,b,c,d,e,f)=>new
Date(a,b,c,d,e,f).getTime(),random_seed:()=>crypto.getRandomValues(new
Int32Array(12)),open:(a,d,c)=>f.openSync(a,N.reduce((a,b,c)=>d&1<<c?a|b:a,0),c),close:a=>f.closeSync(a),write:(a,b,c,d,e)=>f?f.writeSync(a,b,c,d,e===null?e:Number(e)):(console[a===2?"error":"log"](typeof
b==="string"?b:l.decode(b.slice(c,c+d))),d),read:(a,b,c,d,e)=>f.readSync(a,b,c,d,e),file_size:a=>f.fstatSync(a,{bigint:true}).size,register_channel:P,unregister_channel:T,channel_list:B,exit:a=>e&&process.exit(a),argv:()=>e?process.argv.slice(1):["a.out"],on_windows:()=>r,getenv:a=>e?process.env[a]:null,system:a=>{var
b=require("node:child_process").spawnSync(a,{shell:true,stdio:"inherit"});if(b.error)throw b.error;return b.signal?255:b.status},isatty:a=>+require("node:tty").isatty(a),time:()=>performance.now(),getcwd:()=>e?process.cwd():"/static",chdir:a=>process.chdir(a),mkdir:(a,b)=>f.mkdirSync(a,b),rmdir:a=>f.rmdirSync(a),unlink:a=>f.unlinkSync(a),readdir:a=>f.readdirSync(a),stat:(a,b)=>k(f.statSync(a),b),lstat:(a,b)=>k(f.lstatSync(a),b),fstat:(a,b)=>k(f.fstatSync(a),b),file_exists:a=>+f.existsSync(a),is_directory:a=>+f.lstatSync(a).isDirectory(),utimes:(a,b,c)=>f.utimesSync(a,b,c),truncate:(a,b)=>f.truncateSync(a,b),ftruncate:(a,b)=>f.ftruncateSync(a,b),rename:(a,b)=>{var
c;if(r&&(c=f.statSync(b,{throwIfNoEntry:false}))&&f.statSync(a,{throwIfNoEntry:false})?.isDirectory())if(c.isDirectory()){if(!b.startsWith(a))try{f.rmdirSync(b)}catch{}}else{var
d=new
Error(`ENOTDIR: not a directory, rename '${a}' -> '${b}'`);throw Object.assign(d,{errno:-20,code:"ENOTDIR",syscall:"rename",path:b})}f.renameSync(a,b)},throw:a=>{throw a},start_fiber:a=>t(a),suspend_fiber:L((c,b)=>new
Promise(a=>c(a,b))),resume_fiber:(a,b)=>a(b),weak_new:a=>new
WeakRef(a),weak_deref:a=>{var
b=a.deref();return b===undefined?null:b},weak_map_new:()=>new
WeakMap(),map_new:()=>new
Map(),map_get:(a,b)=>{var
c=a.get(b);return c===undefined?null:c},map_set:(a,b,c)=>a.set(b,c),map_delete:(a,b)=>a.delete(b),log:a=>console.log(a)},m={test:a=>+(typeof
a==="string"),compare:(a,b)=>a<b?-1:+(a>b),hash:G,decodeStringFromUTF8Array:()=>"",encodeStringToUTF8Array:()=>0,fromCharCodeArray:()=>""},g=Object.assign({Math:M,bindings:w,js:v,"wasm:js-string":m,"wasm:text-decoder":m,"wasm:text-encoder":m,env:{}},E),s={builtins:["js-string","text-decoder","text-encoder"]};function
K(a){const
b=require("node:path"),c=b.join(b.dirname(require.main.filename),a);return require("node:fs/promises").readFile(c)}const
p=globalThis?.document?.currentScript?.src;function
D(a){const
b=p?new
URL(a,p):a;return fetch(b)}const
J=e?K:D;async function
I(a){return e?WebAssembly.instantiate(await
a,g,s):WebAssembly.instantiateStreaming(a,g,s)}async function
H(){g.OCaml={};const
c=[];async function
b(a,b){const
f=a[1].constructor!==Array;async function
e(){const
d=J(Q+"/"+a[0]+".wasm");await
Promise.all(f?c:a[1].map(a=>c[a]));const
e=await
I(d);Object.assign(b?g.env:g.OCaml,e.instance.exports)}const
d=e();c.push(d);return d}async function
a(a){for(const
c
of
a)await
b(c)}await
b(i[0],1);if(i.length>1){await
b(i[1]);const
c=new
Array(20).fill(i.slice(2).values()).map(a);await
Promise.all(c)}return{instance:{exports:Object.assign(g.env,g.OCaml)}}}const
U=await
H();var{caml_callback:d,caml_alloc_tm:n,caml_alloc_stat:x,caml_start_fiber:A,caml_handle_uncaught_exception:o,caml_buffer:y,caml_extract_string:z,string_get:R,string_set:S,_initialize:j}=U.instance.exports,h=y?.buffer,O=h&&new
Uint8Array(h,0,h.length);t=q(A);var
j=q(j);if(globalThis.process&&globalThis.process.on)globalThis.process.on("uncaughtException",(a,b)=>o(a));else if(globalThis.addEventListener)globalThis.addEventListener("error",a=>a.error&&o(a.error));await
j()})(function(a){"use strict";return{}}(globalThis))({"link":[["code-240724ea37680210daa4",0]],"generated":(a=>{var
c=a,b=a?.module?.export||a;return{"fragments":{"get_Array":a=>a.Array,"get_Date":a=>a.Date,"get_Error":a=>a.Error,"get_JSON":a=>a.JSON,"get_Math":a=>a.Math,"get_Object":a=>a.Object,"get_RegExp":a=>a.RegExp,"get_String":a=>a.String,"get_length":a=>a.length,"js_expr_12c48ca8":()=>a,"js_expr_21711c2a":()=>b,"js_expr_2d7ff750":()=>function(a){throw a},"meth_call_0_toString":a=>a.toString()}}})(globalThis),"src":"fiat_crypto.assets"});
