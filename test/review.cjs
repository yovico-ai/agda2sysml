'use strict';
const fs=require('node:fs'), vm=require('node:vm'), assert=require('node:assert/strict');
const html=fs.readFileSync(process.argv[2],'utf8');
const scripts=[...html.matchAll(/<script([^>]*)>([\s\S]*?)<\/script>/g)];
assert.equal(scripts.length,2,'source escaped the data script');
assert.match(scripts[0][1],/application\/json/);
const data=JSON.parse(scripts[0][2]);
assert(data.declarations.length>0);
const hostile='<img src=x onerror="globalThis.injected=true">';
data.declarations[0].declaration.sourceExcerpt=hostile;

// Exercise the shipped viewer's DOM operations and navigation without network
// or a browser installation. Layout is not asserted by this functional check.
class Element {
 constructor(tag){this.tag=tag;this.children=[];this.textContent='';this.value='';}
 append(...nodes){this.children.push(...nodes);}
 replaceChildren(...nodes){this.children=[...nodes];}
 addEventListener(event,listener){this.listener=listener;}
 set innerHTML(value){throw Error('source must be rendered as text, not HTML');}
}
const ids=Object.fromEntries(['payload','project','summary','search','module','status','count','list','detail'].map(id=>[id,new Element(id)]));
ids.payload.textContent=JSON.stringify(data);
const context={document:{getElementById:id=>ids[id],createElement:tag=>new Element(tag),createTextNode:text=>({textContent:text})},location:{hash:''}};
vm.runInNewContext(scripts[1][2],context,{timeout:5000});
assert.equal(ids.list.children.length,data.declarations.length);
ids.list.children[0].onclick();
const texts=element=>[element.textContent||'',...(element.children||[]).flatMap(texts)];
assert(texts(ids.detail).includes(hostile));
assert.equal(context.injected,undefined);
assert(context.location.hash.includes(encodeURIComponent(data.declarations[0].declaration.symbol)));
ids.search.value='does-not-match-any-declaration';ids.search.listener();
assert.equal(ids.count.textContent,'0 shown');
ids.search.value='';ids.module.value=data.declarations[0].declaration.module;ids.module.listener();
assert.equal(ids.list.children.length,data.declarations.filter(e=>e.declaration.module===ids.module.value).length);
ids.module.value='';ids.status.value='missing';ids.status.listener();
assert.equal(ids.list.children.filter(e=>e.tag==='button').length,data.declarations.filter(e=>e.declaration.requirements.some(r=>r.status==='textual')).length);
ids.status.value='native';ids.status.listener();
const native=data.declarations.filter(e=>e.declaration.nativeTargets.length>0);
assert.equal(ids.list.children.filter(e=>e.tag==='button').length,native.length);
if(native.length){ids.list.children[0].onclick();assert(texts(ids.detail).includes('Generated SysML'));}
console.log('Model review search, filters, navigation, source text and native fragments passed');
