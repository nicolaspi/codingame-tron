#include <iostream>
#include <string>
#include <vector>
#include <list>
#include <cstring>
#include <stdlib.h>
#include <cmath>
#include <iomanip>
#include <time.h>


using namespace std;
#define TOP 0
#define DOWN 1
#define LEFT 2
#define RIGHT 3

#define W 30
#define H 20
int max_depth = 2;
#define ALPHA 0.5
#define BETA 1000
#define GAMMA 0.3
#define LAMBDA 0.1
#define PHI 0.0001
#define TETA 0.1
#define OP_PENALTY 0
#define MAX_DIST 255
#define MAX_OP_DIST_EXPAND 20
long g[H];
long pg[4][H];
unsigned char d[4][H*W];
unsigned char opDist[H*W];
unsigned char pToOpDist[4];
int currentTime;
int playerSpace[4];
long exG[H];
long xInd[30] = {
0x1, //0
0x2, //1
0x4, //2
0x8,
0x10,
0x20,
0x40,
0x80,
0x100,
0x200,
0x400,
0x800,
0x1000,
0x2000,
0x4000,
0x8000,
0x10000,
0x20000,
0x40000,
0x80000,
0x100000,
0x200000,
0x400000,
0x800000,
0x1000000,
0x2000000,
0x4000000,
0x8000000,
0x10000000,
0x20000000
};
/*int complexity_mapper[20] = { //debug
    1,//0
    1,//1
    1,//2
    1,//3
    1,//4
    1,//5
    1,//6
    1,//7
    1,//8
    1,//9
    1,//10
    1,//11
    1,//12
    1,//13
    1,//14
    1,//15
    1,//16
    1,//17
    1,//18
    1 //19
};*/
int complexity_mapper[32] = {
    15,//0
    15,//1
    15,//2
    14,//3
    14,//4
    13,//5
    11,//6
    11,//7
    10,//8
    9,//9
    8,//10
    7,//11
    6,//12
    6,//13
    6,//14
    6,//15
    5,//16
    5,//17
    4,//18
    4,//19
    4,//20
    3,//21
    3,//22
    3,//23
    3,//24
    3,//25
    2,//26
    2,//27
    2,//28
    2,//29
    2,//30
    2
};
unsigned long int compexity_counter;
int players[4*4];
int inGame[4];
char grid[H*W];
char exploredGrid[H*W];
bool isOpponentClose[4];
bool tmpIsOpponentClose[4];
float score;
float baryX;
float baryY;
int N,P;
int* px;
int* py;
long* tmpG;
char* tmpPos;
float worstScore;
int nearestP;

char DX[4] = {0,0,-1,1};
char DY[4] = {-1,1,0,0};
string trans[4] = {"UP","DOWN","LEFT","RIGHT"};

bool getV(long* g, char x, char y) {
    return (g[y] & xInd[x]);
}
void setV(long* g, char x, char y) {
    g[y] = (g[y] | xInd[x]);
}
void unsetV(long* g, char x, char y) {
    g[y] = (g[y] & ~xInd[x]);
}
inline bool isFreeAndValid(long* g, char x, char y) {
    if(x>=0 && x<W && y>=0 && y<H && !getV(g,x,y)) return true;
    return false;
}
inline bool isValid(char x, char y) {
    if(x>=0 && x<W && y>=0 && y<H) return true;
    return false;
}
void printDists(unsigned char * dists){
    cerr << endl;
    for(int y=0;y<H;++y) {
        for(int x=0;x<W;++x) {
            if(dists[x*H+y] == MAX_DIST)
                cerr << '#';
            else
                cerr << min((int)dists[x*H+y],9);
        }
        cerr << endl;
    }
}
void loopRec(bool* posM, int p, char* currentM, char* moves, int& nbMoves) {
    bool moved = false;
    for(char i=0; i<4;++i) {
        //cerr << "extracting possible move player " << p << " move " << trans[i] << " possibility " << posM[4*p+i] << endl;
        if(posM[4*p+i]) {
            currentM[p]=i;
            if(p+1==N){
                memcpy(&moves[nbMoves*N],currentM,N*sizeof(char));
                nbMoves++;
            } else {
                loopRec(posM, p+1, currentM, moves, nbMoves);
            }
            moved = true;
        }
    }
    if(!moved) {
        //No possible moves found
         //cerr << "Not moved player " << p << endl;
         currentM[p]=-1;
         if(p+1==N){
                memcpy(&moves[nbMoves*N],currentM,N*sizeof(char));
                nbMoves++;
          } else {
                loopRec(posM, p+1, currentM, moves, nbMoves);
          }
    }
}
void recCompDist(char x, char y, unsigned char * d, long * g) {
    unsigned char min = MAX_DIST;
    ++compexity_counter;
    if(x>0 && d[(x-1)*H+y]<min) {
        min = d[(x-1)*H+y];
    }
    if(x<W-1 && d[(x+1)*H+y]<min) {
        min = d[(x+1)*H+y];
    }
    if(y>0 && d[x*H+y-1]<min) {
        min = d[x*H+y-1];
    }
    if(y<H-1 && d[x*H+y+1]<min) {
        min = d[x*H+y+1];
    }
    min++;
    d[x*H+y] = min;
    min++;
    if(x>0 && !getV(g,x-1,y) && d[(x-1)*H+y]>min) {
        recCompDist(x-1, y, d, g);
    }
    if(x<W-1 && !getV(g,x+1,y) && d[(x+1)*H+y]>min) {
        recCompDist(x+1, y, d, g);
    }
    if(y>0 && !getV(g,x,y-1) && d[x*H+y-1]>min) {
        recCompDist(x, y-1, d, g);
    }
    if(y<H-1 && !getV(g,x,y+1) && d[x*H+y+1]>min) {
        recCompDist(x, y+1, d, g);
    }
}
void computeDistances(char x,char y, unsigned char * d, long * g) {
    memset(d,MAX_DIST,H*W*sizeof(unsigned char));
    if(x<0)
        return;
    d[x*H+y] = 0;
    if(x>0 && !getV(g,x-1,y)) {
        recCompDist(x-1, y, d, g);
    }
    if(x<W-1 && !getV(g,x+1,y)) {
        recCompDist(x+1, y, d, g);
    }
    if(y>0 && !getV(g,x,y-1)) {
        recCompDist(x, y-1, d, g);
    }
    if(y<H-1 && !getV(g,x,y+1)) {
        recCompDist(x, y+1, d, g);
    }
    //recCompDist(x, y, d, g);
}
void computeDistancesAllPlayers(char * pPos, unsigned char d[][H*W], long * g) {
    for(int i=0;i<N;++i) {
        if(inGame[i])
            computeDistances(pPos[i*2],pPos[i*2+1],d[i],g);
    }
}
void computeDistancesNearPlayer(char * pPos, unsigned char d[][H*W], long * g) {
    computeDistances(pPos[P*2],pPos[P*2+1],d[P],g);
    for(int i=0;i<N;++i) {
        if(i!=P && inGame[i]) {
            if(pToOpDist[i]<MAX_OP_DIST_EXPAND) {
                computeDistances(pPos[i*2],pPos[i*2+1],d[i],g);
            }
        }
    }
}
void computeNearOpDistance(unsigned char d[][H*W], unsigned char * opDist) {
    //TODO check that player is in game
    for(int i=0;i<H*W;++i) {
        unsigned char min = MAX_DIST;
        for(int p=0;p<N;++p) {
            if(p!=P && inGame[p] && pToOpDist[p]<MAX_OP_DIST_EXPAND) {
                if(min>d[p][i])
                    min = d[p][i];
            }
        }
        opDist[i]=min;
    }
}
void computeOpDistance(unsigned char d[][H*W], unsigned char * opDist, int* playerSpace) {
    memset(playerSpace,0,sizeof(int)*N);
    for(int i=0;i<H*W;++i) {
        unsigned char min = MAX_DIST;
        for(int p=0;p<N;++p) {
            if(p!=P && inGame[p]) {
                if(min>d[p][i])
                    min = d[p][i];
                if(d[p][i] < MAX_DIST) {
                    playerSpace[p]++;
                }
            } 
        }
        opDist[i]=min;
        if(d[P][i] < min) {
            playerSpace[P]++;
        }
    }
}
void computePtoOpDistances(char* pPos){
    computeDistances(pPos[2*P],pPos[2*P+1],d[P],g);
    for(int i=0;i<N;++i) {
        if(i!=P){
            if(inGame[i]){
                char x = pPos[2*i];
                char y = pPos[2*i+1];
                unsigned char min = MAX_DIST;
                if(x>0 && d[P][(x-1)*H+y]<min) {
                    min = d[P][(x-1)*H+y];
                }
                if(x<W-1 && d[P][(x+1)*H+y]<min) {
                    min = d[P][(x+1)*H+y];
                }
                if(y>0 && d[P][x*H+y-1]<min) {
                    min = d[P][x*H+y-1];
                }
                if(y<H-1 && d[P][x*H+y+1]<min) {
                    min = d[P][x*H+y+1];
                }
                pToOpDist[i] = min;
            }else{
                pToOpDist[i] = MAX_DIST;
            }
        }
    }
}
void recExpandAround(char x, char y, char pview){

        if(!getV(exG, x,y)) {
            setV(exG, x,y);
            float lscore = 0;
            bool isPlayerPos = false;
           /* if(log)
            cerr << "check x " << (int)(x) << " y " << (int)y << endl;*/
            if(!getV(tmpG, x,y)) {

                ++lscore;
                //Check borders
                if(isFreeAndValid(tmpG,x, y-1)) {
                        ++lscore;
                }
                if(isFreeAndValid(tmpG,x, y+1)) {
                        ++lscore;
                }
                if(isFreeAndValid(tmpG,x-1, y)) {
                        ++lscore;
                }
               if(isFreeAndValid(tmpG,x+1, y)) {
                        ++lscore;
                }
               // lscore -= 0.001*(min((int)x,W-x)+min((int)y, H-y));
                //if(lscore > 3) {
                    if(isValid(x, y-1)) {
                        recExpandAround(x,y-1,pview);
                    }
                     if(isValid(x, y+1)) {
                        recExpandAround(x,y+1,pview);
                    }
                    if(isValid(x-1, y)) {
                        recExpandAround(x-1,y,pview);
                    }
                     if(isValid(x+1, y)) {
                        recExpandAround(x+1,y,pview);
                    }
               // }
                //lscore = lscore;///(distance((char)(index/H),(char)(index%H),(char)*px,(char)*py));
                baryX += lscore * x;
                baryY += lscore * y;
            } else {
                for(char i=0; i<N; ++i) {
                   // cerr << "opp check x " << players[i*4+2] << " y " << players[i*4+3] << endl;
                    if(!isOpponentClose[i]) {
                        //cerr << "opp check x " << players[i*4+2] << " y " << players[i*4+3] << " its grid " << (int)grid[pPos]<< endl;
                        if(x == tmpPos[i*2] &&  y == tmpPos[i*2+1]) {
                            isOpponentClose[i] = true;
                            //cerr << "opp found x " << (int)(index/H) << " y " << index%H << endl;
                            if(i==pview)
                                isPlayerPos = true;
                            else
                                score -= OP_PENALTY;
                        }
                    }
                }
                if(isPlayerPos) {
                    if(isValid(x, y-1)) {
                        recExpandAround(x,y-1,pview);
                    }
                     if(isValid(x, y+1)) {
                        recExpandAround(x,y+1,pview);
                    }
                    if(isValid(x-1, y)) {
                        recExpandAround(x-1,y,pview);
                    }
                     if(isValid(x+1, y)) {
                        recExpandAround(x+1,y,pview);
                    }
                }
            }
            score += lscore;
        }
}
bool freeSegment(long* tmpG,char x, char y, char ox, char oy) {
    char a = x-ox;
    char b = y-oy;
    float incr = 1.0f/max(abs(x-ox),abs(y-oy));
    for(float l = incr; l < 1.0f; l+=incr) {
        if(getV(tmpG,l*a+ox,l*b+oy) && ((char)(l*a) != 0 || (char)(l*b) != 0)){
            return false;
        }
    }
    return true;
}
char freeLocalSpace(long* tmpG, char x,char y) {
    char n=0;
    for(char i=-1;i<2;++i) {
        for(char j=-1;j<2;++j)  {
            if(isValid(i+x,j+y) && !getV(tmpG,i+x,j+y)) {
                ++n;
            }
        }
    }
    return n;
}
char maxFreeLocalSpace(long* tmpG, char x, char y) {
    char max = 0;
    char n;
    for(char i=-1;i<2;++i) {
        for(char j=-1;j<2;++j)  {
            n=freeLocalSpace(tmpG, i+x,j+y);
            if(n>max) {
                max = n;
            }
        }
    }
    return max;
}


float distance(char x0, char y0, char x1, char y1) {
    return (x1-x0)*(x1-x0) + (y1-y0)*(y1-y0);
}

int getDefaultMove() {
    char x,y;
    for(int m = 0;m<4;++m) {
        x = *px+DX[m]; y=*py+DY[m];
        if(isFreeAndValid(g,x,y)) {
            return m;
        }
    }
    return DOWN;
}
class Node {
 public:
     long gr[H];
     char* pPos;
     bool pMode; //to determine max or min
     Node * parent;
     list<Node*> childs;
     float value;
    Node(long* g_, char* pPos_, bool pMode){
        memcpy(gr, g_, sizeof(long)*H);
        this->pPos = new char[2*N];
        memcpy(this->pPos, pPos_, sizeof(char)*2*N);
        //cerr << "pPos "<< static_cast<void *>(this->pPos) << " copied from pPos "<< static_cast<void *>(pPos_) << " in Node(long* g_, char* pPos_, bool pMode)" << endl;
        this->pMode = pMode;
        this->parent = 0;
    }
    Node(const Node& n) {
        //cerr << "Copy constructor "<< endl;
        memcpy(gr, n.gr, sizeof(long)*H);
        this->pPos = new char[2*N];
        memcpy(this->pPos, n.pPos, sizeof(char)*2*N);
        //cerr << "pPos "<< static_cast<void *>(this->pPos) << " copied from pPos "<< static_cast<void *>(n.pPos) << " in Node(const Node& n)" << endl;
        this->pMode = n.pMode;
        this->parent = n.parent;
        this->value = n.value;

    }


    Node(const Node& n, char px, char py) {
        memcpy(gr, n.gr, sizeof(long)*H);
        this->pPos = new char[2*N];
        memcpy(this->pPos, n.pPos, sizeof(char)*2*N);
        //cerr << "pPos "<< static_cast<void *>(this->pPos) << " copied from pPos "<< static_cast<void *>(n.pPos) << " in Node(const Node& n, char px, char py)" << endl;
        this->pPos[P*2] = px;
        this->pPos[P*2+1] = py;
        setV(gr, px, py);
        this->pMode = false;//(!n.pMode);
        this->parent = n.parent;
        this->value = -1000000.0f;//n.value;
    }
    Node(const Node& n, char * npPos, bool * lose) {
        memcpy(gr, n.gr, sizeof(long)*H);
        this->pPos = new char[2*N];
        memcpy(this->pPos, npPos, sizeof(char)*2*N);
       // cerr << "pPos "<< static_cast<void *>(this->pPos) << " copied from pPos "<< static_cast<void *>(npPos) << " in Node(const Node& n, char * npPos)" << endl;
        for(char i=0; i<N;++i) {
            if(inGame[i] && !lose[i])
                setV(gr, this->pPos[i*2], this->pPos[i*2+1]);
            if(lose[i]) {
                for(int x = 0; x < W; ++x){
                    for(int y=0;y<H;++y) {
                        if(getV(pg[i],x,y))
                            unsetV(gr,x,y);
                    }
                }
            }
            //cerr << "setting op pos " << (int)pPos[i*2] << " " << (int)pPos[i*2+1] << " in new Node" << endl;
        }
        this->pMode = true;//(!n.pMode);
        this->parent = n.parent;
        this->value = 1000000.0f;//n.value;
    }
    void addChild(Node* child) {
        //cerr << "pushing child in list pPos "<< static_cast<void *>(child.pPos) << endl;
        childs.push_back(child);
        child->parent = this;
    }

    ~Node() {

            //cerr << "delete "<< static_cast<void *>(pPos) << endl;
            delete[] pPos;
            list<Node*>::iterator it = childs.begin();

            while(it != childs.end()) {
                delete *it;
                it++;
            }


    }
    void printScores(unsigned char* dist, unsigned char* opDist){

    cerr << endl;
    //cerr << setiosflags(ios::fixed | ios::showpoint) << std::setprecision(1);
    for(int y=0;y<H;++y)
        {
        for(int x=0;x<W;++x)
        {
         float opBorderFactor = 1.0f;
            char score='0';
            char hBorders = 0;
            char wBorders = 0;
            char dRBorders = 0;
            char dLBorders = 0;
            int i=x*H+y;
            if(opDist[i]==MAX_DIST && dist[i]<MAX_DIST){
                for(int j=0;j<N;++j){
                            if(j!=P) {
                                if(x>0 && getV(pg[j],x-1,y)){
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(x<W-1 && getV(pg[j],x+1,y)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(y>0 && getV(pg[j],x,y-1)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(y<H-1 && getV(pg[j],x,y+1)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                            }
                        }
                if(x==0 || getV(g,x-1,y)){
                    ++wBorders;
                }
                if(x==W-1 || getV(g,x+1,y)) {
                     ++wBorders;
                }
                if(y==0 || getV(g,x,y-1)) {
                    ++hBorders;
                }
                if(y==H-1 || getV(g,x,y+1)) {
                    ++hBorders;
                }
                if((y==0 && x==0) || getV(g,x-1,y-1)) {
                    ++dRBorders;
                }
                if((y==H-1 && x==W-1) || getV(g,x+1,y+1)) {
                    ++dRBorders;
                }
                 if((y==0 && x==W-1) || getV(g,x+1,y-1)) {
                    ++dLBorders;
                }
                if((y==H-1 && x==0) || getV(g,x-1,y+1)) {
                    ++dLBorders;
                }
                float bonus = (8-hBorders-wBorders-dRBorders-dLBorders)/16.0f;
                score = '+';//hBorders+wBorders+dRBorders+dLBorders;//(0.5f+bonus)*opBorderFactor;

            } else {

                if(opDist[i]<MAX_DIST && dist[i]==MAX_DIST && opDist[i]!=0){
                        score = '-';
                }
                else
                    if(opDist[i]<MAX_DIST && dist[i]<MAX_DIST) {
                        //score += (opDist[i]<=dist[i]?-0.9f:0.9f);//((float)opDist[i]-(float)dist[i])/(H+W);

                        for(int j=0;j<N;++j){
                            if(j!=P) {
                                if(x>0 && getV(pg[j],x-1,y)){
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(x<W-1 && getV(pg[j],x+1,y)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(y>0 && getV(pg[j],x,y-1)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                                if(y<H-1 && getV(pg[j],x,y+1)) {
                                    opBorderFactor = 1.1f;
                                    break;
                                }
                            }
                        }
                        if(opDist[i]==dist[i])
                            score='.';
                        else
                        if(opDist[i]<dist[i]) {
                            score = '-';//opBorderFactor*0.9f;//*1/(0.02f*dist[i]+1);
                        } else {
                            if(x==0 || getV(g,x-1,y)){
                                    ++wBorders;
                            }
                            if(x==W-1 || getV(g,x+1,y)) {
                                 ++wBorders;
                            }
                            if(y==0 || getV(g,x,y-1)) {
                                 ++hBorders;
                            }
                            if(y==H-1 || getV(g,x,y+1)) {
                                 ++hBorders;
                            }if((y==0 && x==0) || getV(g,x-1,y-1)) {
                                ++dRBorders;
                            }
                            if((y==H-1 && x==W-1) || getV(g,x+1,y+1)) {
                                ++dRBorders;
                            }
                             if((y==0 && x==W-1) || getV(g,x+1,y-1)) {
                                ++dLBorders;
                            }
                            if((y==H-1 && x==0) || getV(g,x-1,y+1)) {
                                ++dLBorders;
                            }
                            float bonus = (8-hBorders-wBorders-dRBorders-dLBorders)/1.0f;
                                score = '+';//hBorders+wBorders+dRBorders+dLBorders;//opBorderFactor*(0.4f+bonus);//*1/(0.5f*dist[i]+1);
                        }
                    }
            }
            cerr << score;
        }
        cerr << endl;
        }
         cerr << endl;
    }
    float computeDistScore(unsigned char* dist, unsigned char* opDist, int* playerSpace, long* g, char px, char py) {
        float score = 0.0f;
        float baryX = 0.0f;
        float baryY = 0.0f;
        float territoryPonder = 0.0f;
        for(int i=0;i<W*H;++i) {
            float opBorderFactor = 0.0f;
            char x = i/H;
            char y = i%H;
            char hBorders = 0;
            char wBorders = 0;
            char dRBorders = 0;
            char dLBorders = 0;
            unsigned char distance = dist[i];
            unsigned char opDistance = opDist[i];
            if(opDistance==MAX_DIST && distance<MAX_DIST){
                for(int j=0;j<N;++j){
                            if(j!=P && inGame[j]) {
                                if(x>0 && getV(pg[j],x-1,y)){
                                    opBorderFactor =  /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(x<W-1 && getV(pg[j],x+1,y)) {
                                    opBorderFactor = /*1.0;// /*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(y>0 && getV(pg[j],x,y-1)) {
                                    opBorderFactor = /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(y<H-1 && getV(pg[j],x,y+1)) {
                                    opBorderFactor =  /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                            }
                        }
                if(x==0 || getV(g,x-1,y)){
                    ++wBorders;
                }
                if(x==W-1 || getV(g,x+1,y)) {
                     ++wBorders;
                }
                if(y==0 || getV(g,x,y-1)) {
                    ++hBorders;
                }
                if(y==H-1 || getV(g,x,y+1)) {
                    ++hBorders;
                }
                if((y==0 && x==0) || getV(g,x-1,y-1)) {
                    ++dRBorders;
                }
                if((y==H-1 && x==W-1) || getV(g,x+1,y+1)) {
                    ++dRBorders;
                }
                 if((y==0 && x==W-1) || getV(g,x+1,y-1)) {
                    ++dLBorders;
                }
                if((y==H-1 && x==0) || getV(g,x-1,y+1)) {
                    ++dLBorders;
                }
                float bonus = (8-hBorders-wBorders-dRBorders-dLBorders)/9.0f;
                score += (0.12f+bonus)+opBorderFactor;
                float baryFactor = MAX_DIST-distance;
                territoryPonder += baryFactor;
                baryX += baryFactor*(x);
                baryY += baryFactor*(y);

            } else {

                if(opDistance<MAX_DIST && distance==MAX_DIST){
                    score -= 1.0f;
                }
                else
                    if(opDistance<MAX_DIST && distance<MAX_DIST) {
                        //score += (opDist[i]<=dist[i]?-0.9f:0.9f);//((float)opDist[i]-(float)dist[i])/(H+W);

                        for(int j=0;j<N;++j){
                            if(j!=P && inGame[j]) {
                                if(x>0 && getV(pg[j],x-1,y)){
                                    opBorderFactor =  /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(x<W-1 && getV(pg[j],x+1,y)) {
                                    opBorderFactor =  /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(y>0 && getV(pg[j],x,y-1)) {
                                    opBorderFactor =  /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                                if(y<H-1 && getV(pg[j],x,y+1)) {
                                    opBorderFactor = /*1.0;///*(float)(currentTime+max_depth/2+playerSpace[j])/playerSpace[P];//*/(float)(playerSpace[P]-playerSpace[j])/(playerSpace[P]+playerSpace[j]+1)+1.0f;
                                    break;
                                }
                            }
                        }
                        if(opDistance<distance) {
                            score -= (opBorderFactor+0.012f*max(50-dist[i],1));//*0.9f*1/(0.02f*dist[i]+1);
                        } else {
                            if(opDistance>distance) {
                                if(x==0 || getV(g,x-1,y)){
                                        ++wBorders;
                                }
                                if(x==W-1 || getV(g,x+1,y)) {
                                     ++wBorders;
                                }
                                if(y==0 || getV(g,x,y-1)) {
                                     ++hBorders;
                                }
                                if(y==H-1 || getV(g,x,y+1)) {
                                     ++hBorders;
                                }if((y==0 && x==0) || getV(g,x-1,y-1)) {
                                    ++dRBorders;
                                }
                                if((y==H-1 && x==W-1) || getV(g,x+1,y+1)) {
                                    ++dRBorders;
                                }
                                 if((y==0 && x==W-1) || getV(g,x+1,y-1)) {
                                    ++dLBorders;
                                }
                                if((y==H-1 && x==0) || getV(g,x-1,y+1)) {
                                    ++dLBorders;
                                }
                                float bonus = (8-hBorders-wBorders-dRBorders-dLBorders)/8.0f;
                                score += opBorderFactor+0.5f*(/*0.12f+*/bonus+(1.0f/MAX_DIST)*max(MAX_DIST-dist[i],1));//*1/(0.5f*dist[i]+1);
                                float baryFactor = MAX_DIST-distance;
                                territoryPonder += baryFactor;
                                baryX += baryFactor*(x);
                                baryY += baryFactor*(y);
                            }
                        }
                    }
            }
        }
        baryX/=territoryPonder;
        baryY/=territoryPonder;
        score += (abs(px-baryX)+abs(py-baryY))/1.5f;
        //cerr << " bary dist score : " << (abs(px-baryX)+abs(py-baryY))/10.0f << endl;
        return score;
    }
    void expandNode(char depth, float alpha, float beta) {
        //cerr << "expanding node depth " << (int)depth << " pMode " << this->pMode << endl;
        if(depth == max_depth) {
            //Compute score here
           /* int op;
            float dist;
           // float frees = maxFreeLocalSpace(this->gr, pPos[P*2], pPos[P*2+1]);
            float score = 0.0f;*/
            computeDistancesAllPlayers(this->pPos,d,this->gr);
            computeOpDistance(d,opDist,playerSpace);
            //cerr << "playerSpace P " << playerSpace[P] << endl;
            /*if(nearestP!=P)
                computeDistances(pPos[nearestP*2],pPos[nearestP*2+1],d[nearestP],g);*/

            //computeDistancesNearPlayer(this->pPos,d,this->gr);
            //computeNearOpDistance(d,opDist);

           // printScores(d[P],opDist);
           // cerr << "depth "<< (int)depth << " x "<< (int)this->pPos[2*P] << " y "<< (int)this->pPos[2*P+1] << endl;
            //printDists(opDist);
            //printDists(d[1]);
            this->value = computeDistScore(d[P], opDist,playerSpace, this->gr,this->pPos[P*2],this->pPos[P*2+1]);
            //memcpy(tmpIsOpponentClose,isOpponentClose, N*sizeof(bool));
            /*for(char i=0; i<N;++i) {
                if(i!=P){ //&& tmpIsOpponentClose[i]) {
                    score -= expandAround(*this, pPos[i*2], pPos[i*2+1],i);
                    //cerr << " op score " << score << endl;
                }

            }*/

            /*score += expandAround(*this, pPos[P*2], pPos[P*2+1],(char)P);
            this->value = score;// + PHI * frees;//+depth*5;
            //memcpy(isOpponentClose,tmpIsOpponentClose, N*sizeof(bool));
            checkClosestOpponent(op,dist, this->pPos);
            *///cerr << " free way : "<< freeSegment(this->gr,pPos[P*2], pPos[P*2+1], pPos[op*2], pPos[op*2+1]) << endl;
            //if(op>=0 /*&& freeSegment(this->gr,pPos[P*2], pPos[P*2+1], pPos[op*2], pPos[op*2+1])*/) {
            //    this->value -= GAMMA*dist;
                //cerr << "dist penalty " << GAMMA*dist  << endl;
            //}
            //this->value -= TETA * (distance(pPos[P*2],pPos[P*2+1],(char)baryX,(char)baryY)+1);

            //cerr << "Center distance : " << TETA * 1/(distance(pPos[P*2],pPos[P*2+1],15,10)+1) << endl;
            //cerr << "Node evaluation, got " << this->value  << endl;
            //cerr << "free space " << (int)frees << " pos x " << (int)pPos[P*2] << " y " << (int)pPos[P*2+1] << endl;
            //cerr << "dist " << dist << " 1/dist " << 1/dist << endl;
            return;
        }
       if(pMode) { //player to move
            bool foundMove = false;
            char x = pPos[P*2];
            char y = pPos[P*2+1];
            for(int m=0;m<4; ++m) {
                if(isFreeAndValid(gr,x+DX[m], y+DY[m])) {
                    Node* n =  new Node(*this,x+DX[m],y+DY[m]);
                    addChild(n);
                    foundMove = true;
                   // cerr << "Player move  " << trans[m] << " DEPTH "<< depth << endl;
                }
            }
            if(foundMove == false) {
                this->value = -1000000.0f + depth;
            }
       } else { //opponents
            bool lose[N];
            memset(lose,0,N*sizeof(bool));
            bool posM[N*4];
            memset(posM, false, sizeof(bool)*N*4);
            for(int i = 0; i<N; ++i) {
                bool foundMove = false;
               // cerr << "Opp  " << i << endl;
                if(i!=P && inGame[i]){
                    char x = pPos[i*2];
                    char y = pPos[i*2+1];
                    //cerr << "Opp pos " << (int)x<< " " << (int)y << endl;
                    for(int m=0;m<4; ++m) {
                        bool val = isFreeAndValid(gr,x+DX[m], y+DY[m]);
                        if(pToOpDist[i]<MAX_OP_DIST_EXPAND) {
                            posM[i*4+m] = val;
                        }
                        if(val) {
                            foundMove = true;
                            if(/*i==nearestP){// &&*/ pToOpDist[i]<MAX_OP_DIST_EXPAND) {
                                break;
                            }
                        }
                     //   cerr << "possibility op move " << posM[i*4+m] << " " << trans[m] << " op "<< i << endl;
                    }
                    if(!foundMove) {
                        lose[i]=true;
                    }
                }
            }
            ///Build moves here
            char currentM[N];
            char moves[256];
            int nbMoves = 0;
            char npPos[2*N];

            loopRec(posM, 0, currentM, moves, nbMoves);
            //cerr << "extracted moves " << nbMoves << endl;
            for(char i=0; i<nbMoves; ++i) {
                //cerr << "==>Extracted op move "<< endl;
                for(int p=0; p<N; ++p) {
                    if(inGame[p]){
                        if(moves[i*N+p]>=0) {
                            npPos[p*2] = pPos[p*2] + DX[moves[i*N+p]];
                            npPos[p*2+1] = pPos[p*2+1] + DY[moves[i*N+p]];
                            //cerr << "op move " << trans[moves[i*N+p]] << " op "<< p << endl;
                        } else {

                            if(p!=P && lose[p]){
                                npPos[p*2] = -1;
                                npPos[p*2+1] = -1;
                            } else {
                                npPos[p*2] = pPos[p*2];
                                npPos[p*2+1] = pPos[p*2+1];
                            }
                            //cerr << "move still player "<< p << endl;
                        }
                    }
                }
                Node* n = new Node(*this,npPos, lose);
                addChild(n);
            }
       }
       list<Node*>::iterator it = childs.begin();
       float childScore;
       while(it != childs.end()) {
            (*it)->expandNode(depth+1, alpha,beta);
            childScore = (*it)->value;
            if(!this->pMode){
                if(childScore<alpha){ //prune it
                    //cerr << "alpha pruned " << childScore << "  alpha " << alpha << endl;
                    break;
                }
                if(childScore<beta && childScore>beta) {
                    beta = childScore;
                    //cerr << "new beta " << beta << endl;
                }
            }
            if(this->pMode)
            {
                if(childScore>beta) {//prune it
                    //cerr << "beta pruned " << childScore << "  beta " << beta << endl;
                    //cerr << "beta pruned " << childScore << endl;
                    break;
                }
                //else
                //    beta = childScore;
                if(childScore>alpha && childScore<beta) {
                    alpha = childScore;
                    //cerr << "new alpha " << alpha << endl;
                }
            }
            it++;
       }
       //get scores
       Node* n;
       if(pMode) {
        this->value = getMaxOfChilds(&n);
       } else {
        this->value = getMinOfChilds();
       }
    }
    float getMinOfChilds() {
        if(childs.empty())
            return this->value;
        float minScore = 1000000.0f;
        list<Node*>::iterator it = childs.begin();
       while(it != childs.end()) {
            if((*it)->value<minScore) {
                minScore = (*it)->value;

            }
            it++;
       }
        return minScore;
    }
    int extractPlayerMove(Node* child) {
        char cx = child->pPos[P*2];
        char cy = child->pPos[P*2+1];
        char x = pPos[P*2];
        char y = pPos[P*2+1];
        //cerr << " extract move x " << x << " y " << y << "  cx " << cx << " cy " << cy << endl;
        if(cy != y) {
            if(cy>y) {
                return DOWN;
            }
            return TOP;
        }
        if(cx>x) {
            return RIGHT;
        }
        return LEFT;
    }
    int extractBestMove(float& sCore) {
        Node* n = 0;
        float s = getMaxOfChilds(&n);
        sCore = s;
        cerr << "e " << s << endl;
        if(n)
            return extractPlayerMove(n);
        return getDefaultMove();
    }
    float getMaxOfChilds(Node** node) {
        if(childs.empty())
            return this->value;
        float maxScore = -1000000.0f;
        list<Node*>::iterator it = childs.begin();
           while(it != childs.end()) {
                if((*it)->value>maxScore) {
                    maxScore = (*it)->value;
                    *node = *it;
                }
                it++;
           }
        return maxScore;
    }
    void printChildsScoresAndNodeLeafs(){
        list<Node*>::iterator it = childs.begin();
        while(it != childs.end()) {
            cerr << "child score : " << (*it)->value << endl;
            cerr << "Move : " << trans[extractPlayerMove(*it)] << endl;
            (*it)->extractBestNodeLeaf()->printScores();
            cerr << endl;
            it++;
        }
    }
    Node* extractBestNodeLeaf() {
       if(childs.empty()) return this;
       float maxScore = -1000000.0f;
       float minScore = 1000000.0f;
       Node* pn=0;

       list<Node*>::iterator it = childs.begin();

           while(it != childs.end()) {
                 if(this->pMode) {
                    if((*it)->value>maxScore) {
                        maxScore = (*it)->value;
                        pn = *it;
                    }
                 } else {
                    if((*it)->value<minScore) {
                        minScore = (*it)->value;
                        pn = *it;
                    }
                 }
                it++;
           }
        return pn->extractBestNodeLeaf();
    }
    void printScores(){
        computeDistancesAllPlayers(this->pPos,d,this->gr);
        computeOpDistance(d,opDist,playerSpace);
        printScores(d[P],opDist);
    }
    float expandAround(Node& n, char x, char y, char pview) {
        memset(isOpponentClose,false, 4*sizeof(bool));
        memset(exG,0, H*sizeof(long));
        tmpG = n.gr;
        tmpPos = n.pPos;
        score = 0.0f;
        baryX = 0.0f;
        baryY = 0.0f;
        recExpandAround(x,y, pview);
        if(score) {
            baryX = baryX/score;
            baryY = baryY/score;
        }
        return score;
    }
};





inline bool isFreeAndValid(char x, char y) {
    if(x>=0 && x<W && y>=0 && y<H && !grid[x*H+y]) return true;
    return false;
}






inline bool isValidMove(int m) {
    char x = *px + DX[m];
    char y = *py + DY[m];
    if(x>=0 && x<W && y>=0 && y<H && !grid[x*H+y]) return true;
    return false;
}
void printGrid() {
    cerr << endl;
    for(int i=0;i<H;++i) {
        for(int j =0; j<W;++j) {
                if(getV(g,j,i)) {
                    cerr << "#";
                } else {
                    cerr << "0";
                }
        }
        cerr << endl;
    }
    cerr << endl;
}

void move(int move) {
    cout << trans[move] << endl;
}

int getMoveToward(char X, char Y) {
    int best = -1;
    float minD = 1000.0f;
    char x,y;
    for(int m = 0;m<4;++m) {
        x = *px+DX[m]; y=*py+DY[m];
        if(isFreeAndValid(x,y)) {
            float d = distance(x,y,X,Y);
            if(d<minD) {
                minD = d;
                best = m;
            }
        }
    }
    return best;
}
bool moveToward(char X, char Y){

    int best = -1;
    float minD = 1000.0f;
    char x,y;
    for(int m = 0;m<4;++m) {
        x = *px+DX[m]; y=*py+DY[m];
        if(isFreeAndValid(x,y)) {
            float d = distance(x,y,X,Y);
            if(d<minD) {
                minD = d;
                best = m;
            }
        }
    }
    if(best>0)
    {
        cerr << "Moving toward " << (int)X << " " << (int)Y << endl;
        cout << trans[best] << endl;
        return true;
    }
    return false;
}
bool defaultMove() {
    char x,y;
    for(int m = 0;m<4;++m) {
        x = *px+DX[m]; y=*py+DY[m];
        if(isFreeAndValid(x,y)) {
            cerr << "default move " << trans[m] << endl;
            cout << trans[m] << endl;
            return true;
        }
    }
    return false;
}

void bestMove() {


    clock_t init;
    double final;
    init = clock();
    char pPos[2*N];
    for(int i=0; i<N;++i) {
        pPos[2*i] = players[i*4+2];
        pPos[2*i+1] = players[i*4+3];
    }
    compexity_counter=0;
    computePtoOpDistances(pPos);
    //printDists(d[P]);
    int count=0;
    for(int i=0;i<N;++i){
        //cerr << "dist op "<< i << " " << (int)pToOpDist[i] << endl;
        if(i!=P && pToOpDist[i]<MAX_OP_DIST_EXPAND && inGame[i]) {
            ++count;
        }
    }
    /*int min=MAX_OP_DIST_EXPAND;
    nearestP = P;
    for(int i=0;i<N;++i){
        //cerr << "dist op "<< i << " " << (int)pToOpDist[i] << endl;
        if(i!=P && pToOpDist[i]<=min && inGame[i]) {
            min = pToOpDist[i];
            nearestP = i;
            count = 1;
        }
    }*/
    //cerr << "nearest "<< nearestP << " d " << (int)pToOpDist[nearestP] << " x " << pPos[2*nearestP] << " y " <<  pPos[2*nearestP+1] << endl;
    cerr << " complexity " << log(compexity_counter)*(count+1) << "c " << count << endl;
    max_depth = complexity_mapper[(int)(log(compexity_counter+1)*(count+1))]-1;

    Node root(g, pPos, true);
    root.expandNode(0,-10000000.0f,10000000.0f);
    float bScore;
    int m = root.extractBestMove(bScore);
    move(m);

    final = 1000.0*(double)(clock()-init)/((double)CLOCKS_PER_SEC);
    cerr << "t " << final << endl;
    /*if(final < 50) {
        max_depth++;
    } else {
        if(final>85)
            max_depth--;
    }*/
    root.printChildsScoresAndNodeLeafs();
    //Node *bn = root.extractBestNodeLeaf();
    //bn->printScores();
    //cerr << "extracted bn score : " << bn->value << endl;
    return;
}


int main()
{
    // Read init information from standard input, if any

    memset(grid, 0, sizeof(char)*W*H);
    memset(g, 0, sizeof(long)*H);
    memset(pg, 0, sizeof(long)*H*4);
    memset(inGame, 1, sizeof(int)*4);
    currentTime = 0;

    //int depth_counter = 0;

    while (1) {
        // Read information from standard input
        //depth_counter++;
        cin >> N >> P;

        /*if(depth_counter*N>170 && max_depth<8) {
         //   max_depth++;
            depth_counter=0;
        }*/
        //max_depth = (max_depth>8?8:max_depth);
        cerr << "secret variable " << max_depth << endl;
        //N =2; P=0;
       // cerr << "got N and P " << N << " " << P << endl;
        for(int i=0;i<N;++i) {
            for(int j=0;j<4;++j) {
                cin >> players[i*4+j];
                //cerr << players[i*4+j] << " ";
            }

            //cerr << endl;
        }

        /*players[0]=0;
        players[1]=0;
        players[2]=0;
        players[3]=0;
        players[4]=5;
        players[5]=5;
        players[6]=5;
        players[7]=5;*/

        px = &(players[P*4+2]);
        py = &(players[P*4+3]);
        for(int i=0;i<N;++i) {
            if(currentTime>0 ) {
                if(players[i*4] != -1) {
                    grid[players[i*4+2]*H+players[i*4+3]] = 1;
                    setV(g, players[i*4+2], players[i*4+3]);
                    setV(pg[i],players[i*4+2], players[i*4+3]);
                } else {
                     if(inGame[i]) {
                        for(char x=0;x<W;++x)
                        for(char y=0;y<H;++y) {
                                if(getV(pg[i],x,y))
                                    unsetV(g,x,y);
                        }
                        inGame[i]=0;
                        //max_depth+=2;
                        //computeDistances(players[P*4+2],players[P*4+3], d[P], g);
                        //printDists(d[P]);

                    }

                }
            } else {
                        setV(g, players[i*4], players[i*4+1]);
                        setV(g, players[i*4+2], players[i*4+3]);
                        setV(pg[i],players[i*4], players[i*4+1]);
                        grid[players[i*4]*H+players[i*4+1]] = 1;
                        grid[players[i*4+2]*H+players[i*4+3]] = 1;
                       // max_depth = 10-2*N;
            }

        }
        //printGrid();
        // Compute logic here
        //Node * tree = new Node()
        //int depth =1000;

        //cout << trans[m] << endl;

        bestMove();
        //cerr << "comp : " << compexity_counter << " " << 280/(log(compexity_counter)*N) << endl;
        //max_depth = 200/(log(compexity_counter)*N);
        //cerr << "Score " << score << "  baryX "<< baryX << " baryY " << baryY << endl;

        // Write action to standard output

        currentTime++;
    }

    return 0;
}
