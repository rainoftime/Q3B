TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle
CONFIG -= qt
CONFIG += c++11
#CONFIG += static

SOURCES += main.cpp \
    ExprToBDDTransformer.cpp \
    UnionFind.cpp \
    VariableOrderer.cpp \
    ExprSimplifier.cpp \
    ExprCostComputer.cpp

HEADERS += \
    ExprToBDDTransformer.h \
    VariableOrderer.h \
    ExprSimplifier.h \
    HexHelper.h \
    ExprCostComputer.h

LIBS += -lz3
#INCLUDEPATH += /usr/local/lib
#LIBS += /usr/local/lib/libbdd.a
LIBS += /usr/local/lib/libbdd.a
#LIBS += /media/xjonas/Data/Development/SMT/NightlyZ3/master/z3/build/libz3.a
#LIBS += -L/usr/local/lib -lbdd
