import os

debug = ARGUMENTS.get('debug', 0)
common_env = Environment()

include_paths = ['../toolkit/include', '../toolkit/lib']
lib_paths = [ '../toolkit', '../toolkit/lib/libff' ]

common_env.Append( CPPPATH = [ os.path.abspath(p) for p in include_paths ] )
#common_env.Append( CCFLAGS = ['-g','-Wall', '-DDEBUG' ] )
if int(debug) == 1 :
        common_env.Append( CCFLAGS = ['-g','-Wall', '-DDEBUG' ] )
else:
        common_env.Append( CCFLAGS = ['-O3','-Wall', '-DNDEBUG'] )
#common_env.Append( CCFLAGS = ['-O3','-Wall','-DNDEBUG'] )
common_env.Append( LIBS=[ 'aig', 'ff' ])
common_env.Append( LIBPATH=[ os.path.abspath(p) for p in lib_paths ] )

Export('common_env')
src_objs = SConscript( 'src/SConscript', 'common_env' )
if src_objs is None : print "src_objs is None"

common_env.Program( 'tester', src_objs  )
