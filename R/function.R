
#'Leveraging external aggregated information for the marginal accelerated failure time model.
#'
#'This function is used to fit marginal AFT models with homogeneous auxiliary Information.
#'Besides, the uncertainty in the auxiliary information is negligible.
#'
#'@param data a data.frame, the column names of the data.frame are id, delta(Censor indicator),
#'Z.1(Covariate), Z.2(Covariate), Z.3(Covariate), Y(Observation time).
#'@param boots.num numeric, the replication of the bootstrap procedure.
#'@param Weight character, the weight function. The following are permitted: logrank, gehan.
#'@param gamma.e 2-variate vector, the auxiliary information
#'@return AuxClustAFT returns a list containing the following components:
#'@return \item{coeffi.AI}{the estimators of coefficients for the proposed GMM estimator.}
#'@return \item{se.AI}{the standard errors of the coefficients estimators for the proposed GMM estimator.}
#'@name AuxClustAFT
#'@examples
#'## estimate parameters
#'# AuxClustAFT(data,boots.num,Weight,gamma.e)


AuxClustAFT<-function(data,boots.num,Weight,gamma.e){

  pw.Survf<-function(s,para,ZZ,TT,delta,n,K){
    e<-as.vector(log(TT)-ZZ%*%para)
    ord<-order(e)
    ei<-e[ord]
    deltai<-delta[ord]
    ei.fai<-unique(ei[deltai==1],fromLast=TRUE)
    riskn<-function(x)
    {
      dimv<-min(which(ei==x)):(sum(K))
      riskn<-length(dimv)
      return(riskn)
    }
    riskv<-sapply(ei.fai,FUN = riskn)
    riskd<-riskv/(riskv+1)
    in.ei<-I(ei.fai<=s)*1
    F.pw<-prod(riskd[in.ei==1])
    return(F.pw)
  }

  omega.f<-function(u,para,ZZ,TT,delta,Weight,n,K){
    e<-as.vector(log(TT)-ZZ%*%para)
    if(Weight=="logrank"){obj<-1}
    if(Weight=="gehan"){obj<-n^(-1)*sum(e>=u)}
    if(Weight=="pw"){obj<-pw.Survf(u,para,ZZ,TT,delta,n,K)}
    return(obj)
  }

  Ex.Matrix<-function(M,n,K){
    N<-sum(K)
    Matri<-matrix(0,N,N)

    K.E<-c(0,K)
    for(i in 1:n){
      indi<-(sum(K.E[1:(i)])+1):sum(K.E[1:(i+1)])
      Matri[indi,indi]<-M[[i]]
    }
    return(Matri)
  }

  Phi.f<-function(para,ZZ,TT,delta,Weight,n,K,CWei){

    e<-as.vector(log(TT)-ZZ%*%para)

    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-sapply(e,function(u){I(e>=u)*1})

    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){sum(I(e>=u)*1)})

    #omega_e: (w(e.11),,w(e.nK)). vector
    omega_e<-sapply(e,function(u){return(omega.f(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-apply(t(t(I.e)*(omega_e*delta*S0.e^(-1))),1,sum)

    m<-length(CWei)

    Phi<-NULL
    for(s in 1:m){
      Phi<-rbind(Phi,n^(-1)*(t(ZZ)%*%Ex.Matrix(CWei[[s]],n,K)%*%(omega_e*delta-Eq.1)))
    }

    return(Phi)
  }

  Psi.f<-function(para,ZZ,TT,delta,Weight,n,K){
    e<-as.vector(log(TT)-ZZ%*%para)

    #omega_e: (w(e.11),,w(e.nK)). vector
    omega_e<-sapply(e,function(u){return(omega.f(u,para,ZZ,TT,delta,Weight,n,K))}) #rep(1,n*K) #

    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){sum(I(e>=u)*1)})

    # S0.e: (S(e.11),,S(e.nK)). vector
    S1.e<-sapply(e,function(u){colSums(ZZ*I(e>=u)*1)})

    Psi<-n^(-1)*colSums((ZZ-t(S1.e)/S0.e)*omega_e*delta)
    return(Psi)
  }

  Snsn.f<-function(para2,ZZ2,TT2,delta2,Weight2,n2,K2,CWei2){
    para<-para2; ZZ<-ZZ2; TT<-TT2; delta<-delta2; Weight<-Weight2; n<-n2; K<-K2; CWei<-CWei2

    e<-as.vector(log(TT)-ZZ%*%para)

    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-sapply(e,function(u){I(e>=u)*1})

    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){sum(I(e>=u)*1)})

    #omega_e: (w(e.11),,w(e.nK)). vector
    omega_e<-sapply(e,function(u){return(omega.f(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-rowSums(t(t(I.e)*(omega_e*delta*S0.e^(-1))))

    ### Calculate Sn
    m<-length(CWei); Sn<-NULL
    for(s in 1:m){
      Sn<-rbind(Sn,n^(-1)*(t(ZZ)%*%Ex.Matrix(CWei[[s]],n,K)%*%(omega_e*delta-Eq.1)))
    }

    #### calculate phi_i
    a.bar<-list()
    for(s in 1:m){
      a.bar<-c(a.bar,list(sapply(e,function(u){t(ZZ)%*%Ex.Matrix(CWei[[s]],n,K)%*%(omega_e[which(e==u)]*I.e[,which(e==u)]*(1/S0.e[which(e==u)]))})))
    }

    K.E<-c(0,K)
    phii<-NULL
    for(s in 1:m){
      a.bars<-a.bar[[s]]
      phii1<-sapply(1:n,function(u){ indi<-(sum(K.E[1:(u)])+1):sum(K.E[1:(u+1)]);
      return(t(ZZ[indi,])%*%CWei[[s]][[u]]%*%(omega_e[indi]*delta[indi]-Eq.1[indi])) })

      phii2<-sapply(1:n,function(u){ indi<-(sum(K.E[1:(u)])+1):sum(K.E[1:(u+1)]);
      return(c(a.bars[,indi]%*%delta[indi])-rowSums(sapply(indi,function(u1){colSums(t(a.bars)*delta*(1/S0.e)*I.e[u1,])})))})

      phii<-rbind(phii,phii1-phii2)
    }

    return(list(Sn,phii))

  }

  CovariAI.f<-function(para,para.g,ZZ,ZZAI,TT,delta,Weight,n,K,CWei){

    Phi.all<-Snsn.f(para2=para,ZZ2=ZZ,TT2=TT,delta2=delta,Weight2=Weight,n2=n,K2=K,CWei2=CWei)
    Phi<-Phi.all[[1]]; phi<-Phi.all[[2]]

    Psi.all<-Snsn.f(para2=para.g,ZZ2=ZZAI,TT2=TT,delta2=delta,Weight2=Weight,n2=n,K2=K,CWei2=list(CWei[[1]]))
    Psi<-Psi.all[[1]]; psi<-Psi.all[[2]]

    U<-rbind(Phi,Psi); ui<-rbind(phi,psi)

    Sig1<-0
    for(i in 1:n){
      Sig1<-Sig1+ui[,i]%*%t(ui[,i])
    }

    out<-n^(-1)*Sig1-U%*%t(U)

    return(out)
  }

  library(mvtnorm)
  library(miscTools)
  library(maxLik)
  library(aftgee)
  library(MASS)

  data1<-data
  Y<-data1$Y;delta<-data1$delta;id<-data1$id;X<-cbind(data1$Z.1,data1$Z.2,data1$Z.3)
  Z<-cbind(data1$Z.2,data1$Z.3); n<-length(as.numeric(table(id))); K<-as.vector(table(id))

  CWei.i1<-list(); CWei.i2<-list()
  for(i in 1:n){
    CWei.i1<-c(CWei.i1,list(diag(1,K[i]))); CWei.i2<-c(CWei.i2,list(matrix(1,K[i],K[i])-diag(1,K[i])))
  }
  CWei0<-list(CWei.i1,CWei.i2)

  ################ The initial value
  para.init<-c(aftgee(Surv(Y,delta)~0+Z.1+Z.2+Z.3,id =id,data=data1,corstr="ind",B =2,binit = "lm")$coef.res)

  ############################# GIFAI auxiliary information #########################

  CovariAI<-CovariAI.f(para=para.init,para.g=gamma.e,ZZ=X,ZZAI=Z,TT=Y,delta=delta,Weight=Weight,n,K,CWei=CWei0)

  QIFAI<-function(para2){
    U1<-Phi.f(para=para2,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,CWei=CWei0)
    U2<-as.matrix(Psi.f(para=gamma.e,ZZ=Z,TT=Y,delta=delta,Weight=Weight,n,K))

    U<-rbind(U1,U2)
    out<-t(U)%*%ginv(CovariAI)%*%U
    return(out)
  }

  est.AI<-optim(par = para.init,fn=QIFAI, method="Nelder-Mead")$par

  #####Variance estimation
  Gamma.AI<-CovariAI.f(para=est.AI,para.g=gamma.e,ZZ=X,ZZAI=Z,TT=Y,delta=delta,Weight=Weight,n,K,CWei=CWei0)
  Phi.value<-Phi.f(para=est.AI,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,CWei=CWei0)

  ##estimate the D
  B.times<-boots.num
  eta.AI<-rmvnorm(B.times,rep(0,length(est.AI)),diag(1,length(est.AI)))
  theta.tilde<-matrix(est.AI,B.times,length(est.AI),byrow = TRUE)+n^(-1/2)*eta.AI
  B.formula1<-t(sapply(1:B.times,function(s){n^(0.5)*
      (Phi.f(para=theta.tilde[s,],ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,CWei=CWei0)-Phi.value)})) # B.times:(p+q)
  B.formula2<-ginv(t(eta.AI)%*%eta.AI)%*%t(eta.AI)
  D<-t(sapply(1:dim(B.formula1)[2],function(s){return(B.formula2%*%B.formula1[,s])}))
  variance.AI<-n^(-1)*ginv(t(rbind(D,matrix(0,dim(Z)[2],dim(D)[2])))%*%ginv(Gamma.AI)%*%
                             rbind(D,matrix(0,dim(Z)[2],dim(D)[2])))

  se.AI<-sqrt(diag(variance.AI))

  result<-list(est.AI,se.AI)
  return(results)

}

