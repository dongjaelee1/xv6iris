#!/usr/bin/env python3
"""Resolve the recurring conflict in claude-notes/projects/app-pipe.md when merging a lane:
keep OUR file, append THEIR '### <LANE>...' Findings blocks that we lack, and copy their tick.
usage: merge-notes.py <LANE-HEADING-PREFIX> [tick: x|~]"""
import subprocess,re,sys
lane=sys.argv[1]; tick=sys.argv[2] if len(sys.argv)>2 else None
p='claude-notes/projects/app-pipe.md'
ours=subprocess.run(['git','show',':2:'+p],capture_output=True,text=True).stdout
theirs=subprocess.run(['git','show',':3:'+p],capture_output=True,text=True).stdout
blocks=re.split(r'(?=^### )', theirs, flags=re.M)
add=[b for b in blocks if b.startswith('### '+lane) and b.split('\n')[0] not in ours]
out=ours.rstrip('\n')+'\n\n'+'\n'.join(b.rstrip('\n')+'\n' for b in add)
if tick:
    out=re.sub(r'- \[[ x~]\] \*\*'+re.escape(lane)+r'\*\*', '- ['+tick+'] **'+lane+'**', out, count=1)
open(p,'w').write(out)
print('appended', len(add), 'block(s)')
