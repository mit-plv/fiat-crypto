(function(a){typeof
globalThis!=="object"&&(this?b():(a.defineProperty(a.prototype,"_T_",{configurable:true,get:b}),_T_));function
b(){var
b=this||self;b.globalThis=b;delete
a.prototype._T_}}(Object));
(w=>async a=>{"use strict";let{link:j,src:t,generated:E}=a;const
h=globalThis?.process?.versions?.node;let
J={cos:Math.cos,sin:Math.sin,tan:Math.tan,acos:Math.acos,asin:Math.asin,atan:Math.atan,cosh:Math.cosh,sinh:Math.sinh,tanh:Math.tanh,acosh:Math.acosh,asinh:Math.asinh,atanh:Math.atanh,cbrt:Math.cbrt,exp:Math.exp,expm1:Math.expm1,log:Math.log,log1p:Math.log1p,log2:Math.log2,log10:Math.log10,atan2:Math.atan2,hypot:Math.hypot,pow:Math.pow,fmod:(a,b)=>a%b},v=[Float32Array,Float64Array,Int8Array,Uint8Array,Int16Array,Uint16Array,Int32Array,Int32Array,Int32Array,Int32Array,Float32Array,Float64Array,Uint8Array,Uint8ClampedArray];const
f=h&&require("fs");let
e=f?.constants,K=f?[e.RDONLY,e.O_WRONLY,e.O_APPEND,e.O_CREAT,e.O_TRUNC,e.O_EXCL,e.O_NONBLOCK]:[];var
b={map:new
WeakMap(),set:new
Set(),finalization:new
FinalizationRegistry(a=>b.set.delete(a))};function
M(a){const
c=new
WeakRef(a);b.map.set(a,c);b.set.add(c);b.finalization.register(a,c,a)}function
N(a){const
c=b.map.get(a);if(c){b.map.delete(a);b.set.delete(c);b.finalization.unregister(a)}}function
B(){return[...b.set].map(a=>a.deref()).filter(a=>a)}var
u;function
n(a,b,c){try{return new
WebAssembly.Function(a,b,c)}catch(f){return b}}const
l=new
TextDecoder("utf-8",{ignoreBOM:1}),C=new
TextEncoder;function
F(a,b){b=Math.imul(b,0xcc9e2d51|0);b=b<<15|b>>>17;b=Math.imul(b,0x1b873593);a^=b;a=a<<13|a>>>19;return(a+(a<<2)|0)+(0xe6546b64|0)|0}function
G(a,b){for(var
c=0;c<b.length;c++)a=F(a,b.charCodeAt(c));return a^b.length}let
x={jstag:WebAssembly.JSTag||new
WebAssembly.Tag({parameters:["externref"],results:[]}),identity:a=>a,from_bool:a=>!!a,get:(a,b)=>a[b],set:(a,b,c)=>a[b]=c,delete:(a,b)=>delete
a[b],instanceof:(a,b)=>a
instanceof
b,typeof:a=>typeof
a,equals:(a,b)=>a==b,strict_equals:(a,b)=>a===b,fun_call:(a,b,c)=>a.apply(b,c),meth_call:(a,b,c)=>a[b].apply(a,c),new_array:a=>new
Array(a),new_obj:()=>({}),new:(a,b)=>new
a(...b),global_this:globalThis,iter_props:(a,b)=>{for(var
c
in
a)if(a.hasOwnProperty(c))b(c)},array_length:a=>a.length,array_get:(a,b)=>a[b],array_set:(a,b,c)=>a[b]=c,read_string:a=>l.decode(new
Uint8Array(i,0,a)),read_string_stream:(a,b)=>l.decode(new
Uint8Array(i,0,a),{stream:b}),append_string:(a,b)=>a+b,write_string:a=>{var
c=0,b=a.length;while(1){let{read:d,written:e}=C.encodeInto(a.slice(c),L);b-=d;if(!b)return e;z(e);c+=d}},ta_create:(a,b)=>new
v[a](b),ta_normalize:a=>a
instanceof
Uint32Array?new
Int32Array(a.buffer,a.byteOffset,a.length):a,ta_kind:b=>v.findIndex(a=>b
instanceof
a),ta_length:a=>a.length,ta_get_f64:(a,b)=>a[b],ta_get_f32:(a,b)=>a[b],ta_get_i32:(a,b)=>a[b],ta_get_i16:(a,b)=>a[b],ta_get_ui16:(a,b)=>a[b],ta_get_i8:(a,b)=>a[b],ta_get_ui8:(a,b)=>a[b],ta_set_f64:(a,b,c)=>a[b]=c,ta_set_f32:(a,b,c)=>a[b]=c,ta_set_i32:(a,b,c)=>a[b]=c,ta_set_i16:(a,b,c)=>a[b]=c,ta_set_ui16:(a,b,c)=>a[b]=c,ta_set_i8:(a,b,c)=>a[b]=c,ta_set_ui8:(a,b,c)=>a[b]=c,ta_fill:(a,b)=>a.fill(b),ta_blit:(a,b)=>b.set(a),ta_subarray:(a,b,c)=>a.subarray(b,c),ta_set:(a,b,c)=>a.set(b,c),ta_new:a=>new
Uint8Array(a),ta_copy:(a,b,c,d)=>a.copyWithin(b,c,d),ta_bytes:a=>new
Uint8Array(a.buffer,a.byteOffset,a.length*a.BYTES_PER_ELEMENT),wrap_callback:a=>function(){var
e=arguments.length;if(e>0){var
b=new
Array(e);for(var
d=0;d<e;d++)b[d]=arguments[d]}else
b=[undefined];return c(a,b.length,b,1)},wrap_callback_args:a=>function(){var
e=arguments.length,d=new
Array(e);for(var
b=0;b<e;b++)d[b]=arguments[b];return c(a,1,[d],0)},wrap_callback_strict:(a,b)=>function(){var
g=arguments.length,e=new
Array(a),f=Math.min(arguments.length,a);for(var
d=0;d<f;d++)e[d]=arguments[d];return c(b,a,e,0)},wrap_callback_unsafe:a=>function(){var
e=arguments.length,d=new
Array(e);for(var
b=0;b<e;b++)d[b]=arguments[b];return c(a,d.length,d,2)},wrap_meth_callback:a=>function(){var
e=arguments.length,b=new
Array(e+1);b[0]=this;for(var
d=0;d<e;d++)b[d+1]=arguments[d];return c(a,b.length,b,1)},wrap_meth_callback_args:a=>function(){var
e=arguments.length,d=new
Array(e);for(var
b=0;b<e;b++)d[b]=arguments[b];return c(a,2,[this,d],0)},wrap_meth_callback_strict:(a,b)=>function(){var
d=new
Array(a+1),f=Math.min(arguments.length,a);d[0]=this;for(var
e=0;e<f;e++)d[e+1]=arguments[e];return c(b,d.length,d,0)},wrap_meth_callback_unsafe:a=>function(){var
e=arguments.length,b=new
Array(e+1);b[0]=this;for(var
d=0;d<e;d++)b[d+1]=arguments[d];return c(a,b.length,b,2)},wrap_fun_arguments:a=>function(){return a(arguments)},format_float:(a,b,c,d)=>{function
j(a,b){if(Math.abs(a)<1.0)return a.toFixed(b);else{var
c=parseInt(a.toString().split("+")[1]);if(c>20){c-=20;a/=Math.pow(10,c);a+=new
Array(c+1).join("0");if(b>0)a=a+"."+new
Array(b+1).join("0");return a}else
return a.toFixed(b)}}switch(b){case
0:var
e=d.toExponential(a),f=e.length;if(e.charAt(f-3)=="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break;case
1:e=j(d,a);break;case
2:a=a?a:1;e=d.toExponential(a-1);var
i=e.indexOf("e"),h=+e.slice(i+1);if(h<-4||d>=1e21||d.toFixed(0).length>a){var
f=i-1;while(e.charAt(f)=="0")f--;if(e.charAt(f)==".")f--;e=e.slice(0,f+1)+e.slice(i);f=e.length;if(e.charAt(f-3)=="e")e=e.slice(0,f-1)+"0"+e.slice(f-1);break}else{var
g=a;if(h<0){g-=h+1;e=d.toFixed(g)}else
while(e=d.toFixed(g),e.length>a+1)g--;if(g){var
f=e.length-1;while(e.charAt(f)=="0")f--;if(e.charAt(f)==".")f--;e=e.slice(0,f+1)}}break}return c?" "+e:e},gettimeofday:()=>new
Date().getTime()/1000,gmtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),e=new
Date(Date.UTC(b.getUTCFullYear(),0,1)).getTime(),d=Math.floor((c-e)/86400000);return o(b.getUTCSeconds(),b.getUTCMinutes(),b.getUTCHours(),b.getUTCDate(),b.getUTCMonth(),b.getUTCFullYear()-1900,b.getUTCDay(),d,false)},localtime:a=>{var
b=new
Date(a*1000),c=b.getTime(),f=new
Date(b.getFullYear(),0,1).getTime(),d=Math.floor((c-f)/86400000),e=new
Date(b.getFullYear(),0,1),g=new
Date(b.getFullYear(),6,1),h=Math.max(e.getTimezoneOffset(),g.getTimezoneOffset());return o(b.getSeconds(),b.getMinutes(),b.getHours(),b.getDate(),b.getMonth(),b.getFullYear()-1900,b.getDay(),d,b.getTimezoneOffset()<h)},mktime:(a,b,c,d,e,f)=>new
Date(a,b,c,d,e,f).getTime(),random_seed:()=>crypto.getRandomValues(new
Int32Array(12)),open:(a,d,c)=>f.openSync(a,K.reduce((a,b,c)=>d&1<<c?a|b:a,0),c),close:a=>f.closeSync(a),write:(a,b,c,d,e)=>f?f.writeSync(a,b,c,d,e==null?e:Number(e)):(console[a==2?"error":"log"](typeof
b=="string"?b:l.decode(b.slice(c,c+d))),d),read:(a,b,c,d,e)=>f.readSync(a,b,c,d,e),file_size:a=>f.fstatSync(a,{bigint:true}).size,register_channel:M,unregister_channel:N,channel_list:B,exit:a=>h&&d.exit(a),argv:()=>h?d.argv.slice(1):["a.out"],getenv:a=>h?d.env[a]:null,system:a=>{var
b=require("child_process").spawnSync(a,{shell:true,stdio:"inherit"});if(b.error)throw b.error;return b.signal?255:b.status},time:()=>performance.now(),getcwd:()=>h?d.cwd():"/static",chdir:a=>d.chdir(a),mkdir:(a,b)=>f.mkdirSync(a,b),unlink:a=>f.unlinkSync(a),readdir:a=>f.readdirSync(a),file_exists:a=>+f.existsSync(a),rename:(a,b)=>f.renameSync(a,b),throw:a=>{throw a},start_fiber:a=>u(a),suspend_fiber:n({parameters:["externref","funcref","eqref"],results:["eqref"]},(c,b)=>new
Promise(a=>c(a,b)),{suspending:"first"}),resume_fiber:(a,b)=>a(b),weak_new:a=>new
WeakRef(a),weak_deref:a=>{var
b=a.deref();return b==undefined?null:b},weak_map_new:()=>new
WeakMap,map_new:()=>new
Map,map_get:(a,b)=>{var
c=a.get(b);return c==undefined?null:c},map_set:(a,b,c)=>a.set(b,c),map_delete:(a,b)=>a.delete(b),log:a=>console.log("ZZZZZ",a)},m={test:a=>+(typeof
a==="string"),compare:(a,b)=>a<b?-1:+(a>b),hash:G,decodeStringFromUTF8Array:()=>"",encodeStringToUTF8Array:()=>0};const
g=Object.assign({Math:J,bindings:x,js:w,"wasm:js-string":m,"wasm:text-decoder":m,"wasm:text-encoder":m,env:{}},E),s={builtins:["js-string","text-decoder","text-encoder"]};function
I(a){const
b=require("path"),c=b.join(b.dirname(require.main.filename),a);return require("fs/promises").readFile(c)}function
D(a){const
b=globalThis?.document?.currentScript?.src,c=b?new
URL(a,b):a;return fetch(c)}const
r=h?I:D;async function
q(a){return h?WebAssembly.instantiate(await
a,g,s):WebAssembly.instantiateStreaming(a,g,s)}async function
H(){g.OCaml={};const
c=[];async function
b(a,b){const
f=a[1].constructor!==Array;async function
e(){const
d=r(t+"/"+a[0]+".wasm");await
Promise.all(f?c:a[1].map(a=>c[a]));const
e=await
q(d);Object.assign(b?g.env:g.OCaml,e.instance.exports)}const
d=e();c.push(d);return d}async function
a(a){for(const
c
of
a)await
b(c)}await
b(j[0],1);await
b(j[1]);const
d=new
Array(20).fill(j.slice(2).values()).map(a);await
Promise.all(d);return{instance:{exports:Object.assign(g.env,g.OCaml)}}}const
O=await(j?H():q(r(t)));var{caml_callback:c,caml_alloc_tm:o,caml_start_fiber:A,caml_handle_uncaught_exception:p,caml_buffer:y,caml_extract_string:z,_initialize:k}=O.instance.exports,i=y?.buffer,L=i&&new
Uint8Array(i,0,i.length);u=n({parameters:["eqref"],results:["externref"]},A,{promising:"first"});var
k=n({parameters:[],results:["externref"]},k,{promising:"first"}),d=globalThis.process;if(d&&d.on)d.on("uncaughtException",(a,b)=>p(a));else if(globalThis.addEventListener)globalThis.addEventListener("error",a=>a.error&&p(a.error));await
k()})(function(a){"use strict";return{}}(globalThis))({"link":0,"generated":(a=>{var
c=a,b=a?.module?.export||a;return{"strings":["Undefined_recursive_module","Assert_failure","Sys_blocked_io","Stack_overflow","Match_failure","Not_found","Division_by_zero","End_of_file","Invalid_argument","Failure","Sys_error","Out_of_memory"],"fragments":{"get_Array":a=>a.Array,"get_Date":a=>a.Date,"get_Error":a=>a.Error,"get_JSON":a=>a.JSON,"get_Math":a=>a.Math,"get_Object":a=>a.Object,"get_RegExp":a=>a.RegExp,"get_String":a=>a.String,"js_expr_12c48ca8":()=>a,"js_expr_21711c2a":()=>b,"js_expr_2d7ff750":()=>function(a){throw a},"meth_call_0_toString":a=>a.toString()}}})(globalThis),"src":"wasm_fiat_crypto.wasm"});
