"""Regenerate draft.md from main.tex for reading on screen: python3 tomd.py (run in paper/, needs pandoc)."""
import re,sys,subprocess,tempfile
sys.argv[1:] = [tempfile.mkdtemp()]
s=open('main.tex').read()
num={'intro':1,'setting':2,'encoding':3,'decision':4,'counting':5,'boundary':6,'conclusion':7}
def cref(m):
    ks=m.group(1).split(',')
    if ks[0].startswith('tab:'): return 'Table 1'
    ns=[str(num[k[4:]]) for k in ks]
    return ('Section ' if len(ns)==1 else 'Sections ')+' and '.join(ns)
s=re.sub(r'\\Cref\{([^}]*)\}',cref,s)
s=re.sub(r'\\lstinline\{([^}]*)\}',r'\\texttt{\1}',s)
s=s.replace('\\begin{lstlisting}','\\begin{verbatim}').replace('\\end{lstlisting}','\\end{verbatim}')
s=s.replace('\\subparagraph*','\\paragraph')
s=re.sub(r'\\author\{.*\n','',s)
open(sys.argv[1]+'/pd.tex','w').write(s)
body=subprocess.run(['pandoc',sys.argv[1]+'/pd.tex','-f','latex','-t','gfm','--citeproc',
  '--bibliography=../docs/paper-refs.bib','--bibliography=extra.bib','--number-sections',
  '--metadata','link-citations=true'],capture_output=True,text=True,check=True).stdout
ab=re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}',s,re.S).group(1)
abmd=subprocess.run(['pandoc','-f','latex','-t','gfm'],input=ab,capture_output=True,text=True,check=True).stdout
head=("# Machine-Checked Complexity of Decision-Table Completeness in Lean\n\n"
"Carlos A. Russell, Independent Researcher, Buenos Aires, Argentina\n"
"(carlos.a.russell@gmail.com, ORCID 0009-0003-3741-0230)\n\n"
"> First draft, generated from `paper/main.tex` with pandoc for reading on screen. The LaTeX file\n"
"> is the source; edit it, not this file. Not compiled with LaTeX yet.\n\n"
"**Abstract.** "+abmd.strip()+"\n\n")
body=re.sub(r'^# ', '## ', body, flags=re.M)
body=re.sub(r'^#### ', '#### ', body, flags=re.M)
body=body.replace('<div id="refs"','## References\n\n<div id="refs"',1)
open('draft.md','w').write(head+body)
t=open('draft.md').read(); i=[0]
def n(m):
    if m.group(1)=='References': return m.group(0)
    i[0]+=1; return '## %d %s'%(i[0],m.group(1))
t=re.sub(r'^## (.+)$',n,t,flags=re.M)
open('draft.md','w').write(t)
