import VersoBlog
import ReasBookSite.Home
import ReasBookSite.LiterateModule
import ReasBookSite.Sections
import ReasBookSite.RouteTable
import Book

open Verso Genre Blog Site Syntax
open ReasBookSite.RouteTable
open scoped ReasBookSite.RouteTable

open Output Html Template Theme

def siteRoot : String := "/ReasBook/"
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""

def navScript : String :=
  "(function(){" ++
  "const siteRoot=(window.__versoSiteRoot||'/').replace(/\\/+$/,'')+'/';" ++
  "const abs=u=>new URL(u,window.location.origin);" ++
  "const withRoot=p=>siteRoot+p.replace(/^\\/+/, '');" ++
  "for(const a of document.querySelectorAll('a[href]')){" ++
  "const href=a.getAttribute('href');if(!href)continue;" ++
  "if(href.startsWith('#')||href.startsWith('mailto:')||href.startsWith('tel:'))continue;" ++
  "let u;try{u=abs(href);}catch(_){continue;}" ++
  "if(u.origin!==window.location.origin)continue;" ++
  "if(!u.pathname.startsWith(siteRoot)){" ++
  "const normalized=withRoot(u.pathname);" ++
  "a.setAttribute('href',normalized+u.search+u.hash);" ++
  "}" ++
  "}" ++
  "const nav=document.querySelector('nav.top ol');if(!nav)return;" ++
  "const links=[...nav.querySelectorAll('li > a')];" ++
  "const dirLinks=links.filter(a=>{const u=abs(a.href);const p=u.pathname;return p.includes('/books/')||p.includes('/papers/');});" ++
  "if(!dirLinks.length)return;" ++
  "const tree={books:{},papers:{}};" ++
  "for(const a of dirLinks){" ++
  "const u=abs(a.href);" ++
  "let p=u.pathname;if(!p.startsWith(siteRoot))continue;" ++
  "p=p.slice(siteRoot.length).replace(/^\\/+/, '');" ++
  "const segs=p.split('/').filter(Boolean);" ++
  "if(segs.length<3)continue;" ++
  "if(segs[0]==='books'){" ++
  "const book=segs[1];const chapIdx=segs.indexOf('chapters');if(chapIdx===-1||segs.length<=chapIdx+2)continue;" ++
  "const chap=segs[chapIdx+1];const leaf=segs[chapIdx+2];" ++
  "tree.books[book]=tree.books[book]||{href:withRoot('books/'+book+'/'),chapters:{}};" ++
  "tree.books[book].chapters[chap]=tree.books[book].chapters[chap]||[];" ++
  "tree.books[book].chapters[chap].push({href:a.getAttribute('href')||a.href,text:a.textContent||leaf,leaf});" ++
  "}else if(segs[0]==='papers'){" ++
  "const paper=segs[1];const secIdx=segs.indexOf('sections');if(secIdx===-1||segs.length<=secIdx+1)continue;" ++
  "const leaf=segs[secIdx+1];" ++
  "tree.papers[paper]=tree.papers[paper]||{href:withRoot('papers/'+paper+'/paper/'),sections:[]};" ++
  "tree.papers[paper].sections.push({href:a.getAttribute('href')||a.href,text:a.textContent||leaf,leaf});" ++
  "}" ++
  "}" ++
  "const slug=s=>s.replace(/_/g,' ').replace(/\\b\\w/g,m=>m.toUpperCase());" ++
  "const navRoot=document.createElement('li');navRoot.className='nav-tree-root';" ++
  "const current=window.location.pathname;" ++
  "const makeDetails=(title,open)=>{const d=document.createElement('details');if(open)d.open=true;const s=document.createElement('summary');s.textContent=title;d.appendChild(s);return d;};" ++
  "const booksOpen=current.includes('/books/');const books=makeDetails('Books',booksOpen);" ++
  "for(const book of Object.keys(tree.books).sort()){" ++
  "const bookOpen=current.includes('/books/'+book+'/');const b=makeDetails(slug(book),bookOpen);" ++
  "const chapters=tree.books[book].chapters;" ++
  "for(const chap of Object.keys(chapters).sort()){" ++
  "const chapOpen=current.includes('/'+chap+'/');const c=makeDetails(chap.replace(/^chap/i,'Chapter '),chapOpen);" ++
  "const ul=document.createElement('ul');for(const x of chapters[chap].sort((x,y)=>x.leaf.localeCompare(y.leaf))){const li=document.createElement('li');const a=document.createElement('a');a.href=x.href;a.textContent=x.text;li.appendChild(a);ul.appendChild(li);}c.appendChild(ul);b.appendChild(c);" ++
  "}" ++
  "books.appendChild(b);" ++
  "}" ++
  "const papersOpen=current.includes('/papers/');const papers=makeDetails('Papers',papersOpen);" ++
  "for(const paper of Object.keys(tree.papers).sort()){" ++
  "const paperOpen=current.includes('/papers/'+paper+'/');const p=makeDetails(slug(paper),paperOpen);" ++
  "const ul=document.createElement('ul');for(const x of tree.papers[paper].sections.sort((x,y)=>x.leaf.localeCompare(y.leaf))){const li=document.createElement('li');const a=document.createElement('a');a.href=x.href;a.textContent=x.text;li.appendChild(a);ul.appendChild(li);}p.appendChild(ul);papers.appendChild(p);" ++
  "}" ++
  "navRoot.appendChild(books);navRoot.appendChild(papers);nav.appendChild(navRoot);" ++
  "for(const a of dirLinks){const li=a.closest('li');if(li)li.remove();}" ++
  "})();"

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href="/ReasBook/static/style.css"/>
          <script>{{ siteRootScript }}</script>
          <script>{{ navScript }}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation">
                <ol>
                  <li><a href="/ReasBook/">"Home"</a></li>
                  <li><a href="/ReasBook/docs/">"Documentation"</a></li>
                  {{ ← dirLinks (← read).site }}
                </ol>
              </nav>
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
}
|>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

/-- Generated section routes are injected by `reasbook_site_dir` from `ReasBookSite.RouteTable`. -/
def demoSite : Site := reasbook_site

def docsBaseUrl : String := "https://optsuite.github.io/ReasBook/docs/"

def linkTargets : Code.LinkTargets α where
  const name _ := #[mkLink s!"{docsBaseUrl}find?pattern={name}#doc"]
  definition name _ := #[mkLink s!"{docsBaseUrl}find?pattern={name}#doc"]
where
  mkLink href := { shortDescription := "doc", description := "API documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
