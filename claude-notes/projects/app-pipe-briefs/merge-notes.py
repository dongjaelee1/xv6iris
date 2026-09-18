#!/usr/bin/env python3
"""After `git merge app-pipe/<lane>` (conflicted OR clean), rebuild claude-notes/projects/app-pipe.md as:
OUR pre-merge version + THEIR '### <LANE>...' Findings blocks we lack + their tick.
usage: merge-notes.py <LANE-HEADING-PREFIX> <branch> [tick: x|~]
ours = index stage 2 if conflicted, else ORIG_HEAD (the pre-merge main); theirs = <branch>."""
import subprocess,re,sys
lane=sys.argv[1]; branch=sys.argv[2]; tick=sys.argv[3] if len(sys.argv)>3 else None
p='claude-notes/projects/app-pipe.md'
r=subprocess.run(['git','show',':2:'+p],capture_output=True,text=True)
ours=r.stdout if r.returncode==0 and r.stdout.strip() else subprocess.run(['git','show','ORIG_HEAD:'+p],capture_output=True,text=True).stdout
theirs=subprocess.run(['git','show',branch+':'+p],capture_output=True,text=True).stdout
assert len(ours)>1000 and len(theirs)>1000, "refusing: a side is empty"
blocks=re.split(r'(?=^### )', theirs, flags=re.M)
add=[b for b in blocks if b.startswith('### '+lane) and b.split('\n')[0] not in ours]
out=ours.rstrip('\n')+'\n\n'+''.join(b.rstrip('\n')+'\n' for b in add)
if tick: out=re.sub(r'- \[[ x~]\] \*\*'+re.escape(lane)+r'\*\*','- ['+tick+'] **'+lane+'**',out,count=1)
open(p,'w').write(out); print('appended',len(add),'block(s); ours from', 'index' if r.returncode==0 and r.stdout.strip() else 'ORIG_HEAD')
