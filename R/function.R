
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

  pw.Survf<-function(s,para,ZZ,TT,delta,n,K)
  {
    e<-as.vector(log(TT)-ZZ%*%para)
    ord<-order(e)
    ei<-e[ord]
    deltai<-delta[ord]
    ei.fai<-unique(ei[deltai==1],fromLast=TRUE)
    riskn<-function(x)
    {
      dimv<-min(which(ei==x)):(K*n)
      riskn<-length(dimv)
      return(riskn)
    }
    riskv<-sapply(ei.fai,FUN = riskn)
    riskd<-riskv/(riskv+1)
    in.ei<-I(ei.fai<=s)*1
    F.pw<-prod(riskd[in.ei==1])
    return(F.pw)
  }

  phi<-function(u,para,ZZ,TT,delta,Weight,n,K)
  {
    e<-as.vector(log(TT)-ZZ%*%para)
    if(Weight=="logrank"){obj<-1}
    if(Weight=="gehan"){obj<-n^(-1)*sum(e>=u)}
    if(Weight=="pw"){obj<-pw.Survf(u,para,ZZ,TT,delta,n,K)}
    return(obj)
  }

  C_l<-function(M,n,K)
  {
    Matri<-matrix(0,K*n,K*n)
    for(i in 1:n)
    {
      Matri[((i-1)*K+1):(i*K),((i-1)*K+1):(i*K)]<-M
    }
    return(Matri)
  }


  Phi.f<-function(para,ZZ,TT,delta,Weight,n,K){

    C.11<-diag(1,K); C.12<-matrix(1,K,K)-diag(1,K)

    e<-as.vector(log(TT)-ZZ%*%para)
    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-matrix(unlist(lapply(e,function(u){return(I(e>=u)*1)})), nrow=n*K,ncol=n*K)
    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){return(sum(e>=u))})
    #phi_e: (w(e.11),,w(e.nK)). vector
    phi_e<-sapply(e,function(u){return(phi(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-apply(t(t(I.e)*(phi_e*delta*S0.e^(-1))),1,sum)

    Sn.11<-n^(-1)*(t(ZZ)%*%C_l(C.11,n,K)%*%(phi_e*delta-Eq.1))
    Sn.12<-n^(-1)*(t(ZZ)%*%C_l(C.12,n,K)%*%(phi_e*delta-Eq.1))
    Sn<-rbind(Sn.11,Sn.12)

    return(Sn)
  }

  Covari.f<-function(para,d,ZZ,TT,delta,Weight,n,K){

    C.11<-diag(1,K); C.12<-matrix(1,K,K)-diag(1,K)

    e<-as.vector(log(TT)-ZZ%*%para)
    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-matrix(unlist(lapply(e,function(u){return(I(e>=u)*1)})), nrow=n*K,ncol=n*K)
    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){return(sum(e>=u))})
    #phi_e: (w(e.11),,w(e.nK)). vector
    phi_e<-sapply(e,function(u){return(phi(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-apply(t(t(I.e)*(phi_e*delta*S0.e^(-1))),1,sum)

    Sn.11<-n^(-1)*(t(ZZ)%*%C_l(C.11,n,K)%*%(phi_e*delta-Eq.1))
    Sn.12<-n^(-1)*(t(ZZ)%*%C_l(C.12,n,K)%*%(phi_e*delta-Eq.1))
    Sn<-rbind(Sn.11,Sn.12)-d

    phii<-function(MM){

      # a.matrix: (a11(e11),,anK(e11),,a11(enK),,anK(enK)) matrix
      a.matrix<-t(t(matrix(as.vector(t(ZZ)%*%C_l(MM,n,K)),dim(ZZ)[2],n*K*n*K))*rep(phi_e,each=n*K))

      I.e.vector<-as.vector(I.e)
      Eq.4<-t(t(a.matrix)*I.e.vector)

      # a.bar: (a.bar(e11),,a.bar(enK)) matrix
      a.bar<-NULL
      for(i in 1:(n*K)){
        a.bar<-cbind(a.bar,apply(Eq.4[,((i-1)*n*K+1):(i*n*K)],1,sum)/S0.e[i])
      }

      Eq.5<-t(t(a.bar)*delta*S0.e^(-1))

      Eq.2<-NULL
      for(i in 1:n){

        Eq.3<-t(ZZ)[,((i-1)*K+1):(i*K)]%*%MM%*%
          (phi_e[((i-1)*K+1):(i*K)]*delta[((i-1)*K+1):(i*K)]-Eq.1[((i-1)*K+1):(i*K)])

        Eq.6<-apply(t(t(a.bar[,((i-1)*K+1):(i*K)])*delta[((i-1)*K+1):(i*K)]),1,sum)-
          apply(t(t(Eq.5)*apply(I.e[((i-1)*K+1):(i*K),],2,sum)),1,sum)

        phi.i<-Eq.3-Eq.6
        Eq.2<-cbind(Eq.2,phi.i)
      }

      return(Eq.2)
    }

    phiall<-rbind(phii(C.11),phii(C.12))-d

    Sig1<-0
    for(i in 1:n){
      Sig1<-Sig1+phiall[,i]%*%t(phiall[,i])
    }

    out<-n^(-1)*Sig1-Sn%*%t(Sn)

    return(out)
  }


  Sn.f<-function(para,ZZ,TT,delta,Weight,n,K,MA){

    e<-as.vector(log(TT)-ZZ%*%para)
    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-matrix(unlist(lapply(e,function(u){return(I(e>=u)*1)})), nrow=n*K,ncol=n*K)
    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){return(sum(e>=u))})
    #phi_e: (w(e.11),,w(e.nK)). vector
    phi_e<-sapply(e,function(u){return(phi(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-apply(t(t(I.e)*(phi_e*delta*S0.e^(-1))),1,sum)

    out<-n^(-1)*(t(ZZ)%*%C_l(MA,n,K)%*%((phi_e*delta-Eq.1)))

    return(out)
  }

  u.f<-function(para,ZZ,TT,delta,Weight,n,K,MA){

    e<-as.vector(log(TT)-ZZ%*%para)
    # I.e: matrix(I(e>=e.11),,I(e>=e.nK)), the first col is I(e>=e.11). matrix
    I.e<-matrix(unlist(lapply(e,function(u){return(I(e>=u)*1)})), nrow=n*K,ncol=n*K)
    # S0.e: (S(e.11),,S(e.nK)). vector
    S0.e<-sapply(e,function(u){return(sum(e>=u))})
    #phi_e: (w(e.11),,w(e.nK)). vector
    phi_e<-sapply(e,function(u){return(phi(u,para,ZZ,TT,delta,Weight,n,K))})

    Eq.1<-apply(t(t(I.e)*(phi_e*delta*S0.e^(-1))),1,sum)

    phii<-function(MM){

      # a.matrix: (a11(e11),,anK(e11),,a11(enK),,anK(enK)) matrix
      a.matrix<-t(t(matrix(as.vector(t(ZZ)%*%C_l(MM,n,K)),dim(ZZ)[2],n*K*n*K))*rep(phi_e,each=n*K))

      I.e.vector<-as.vector(I.e)
      Eq.4<-t(t(a.matrix)*I.e.vector)

      # a.bar: (a.bar(e11),,a.bar(enK)) matrix
      a.bar<-NULL
      for(i in 1:(n*K)){
        a.bar<-cbind(a.bar,apply(Eq.4[,((i-1)*n*K+1):(i*n*K)],1,sum)/S0.e[i])
      }

      Eq.5<-t(t(a.bar)*delta*S0.e^(-1))

      Eq.2<-NULL
      for(i in 1:n){

        Eq.3<-t(ZZ)[,((i-1)*K+1):(i*K)]%*%MM%*%
          (phi_e[((i-1)*K+1):(i*K)]*delta[((i-1)*K+1):(i*K)]-Eq.1[((i-1)*K+1):(i*K)])

        Eq.6<-apply(t(t(a.bar[,((i-1)*K+1):(i*K)])*delta[((i-1)*K+1):(i*K)]),1,sum)-
          apply(t(t(Eq.5)*apply(I.e[((i-1)*K+1):(i*K),],2,sum)),1,sum)

        phi.i<-Eq.3-Eq.6
        Eq.2<-cbind(Eq.2,phi.i)
      }

      return(Eq.2)
    }

    out<-phii(MA)


    return(t(t(out)))
  }

  CovariAI.f<-function(para,d,ZZ,ZZAI,TT,delta,Weight,n,K,gamma){

    C.11<-diag(1,K); C.12<-matrix(1,K,K)-diag(1,K)

    u1<-u.f(para=para,ZZ=ZZ,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.11)
    u2<-u.f(para=para,ZZ=ZZ,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.12)
    u3<-u.f(para=gamma,ZZ=ZZAI,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.11)
    u<-rbind(u1,u2,u3)-d
    U1<-Sn.f(para=para,ZZ=ZZ,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.11)
    U2<-Sn.f(para=para,ZZ=ZZ,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.12)
    U3<-Sn.f(para=gamma,ZZ=ZZAI,TT=TT,delta=delta,Weight=Weight,n,K,MA=C.11)
    U<-rbind(U1,U2,U3)-d
    out<--U%*%t(U)
    for(s in 1:n){
      out<-out+n^(-1)*u[,s]%*%t(u[,s])
    }

    return(out)
  }

  library(miscTools)
  library(maxLik)
  library(aftgee)
  library(MASS)

  data1<-data
  Y<-data1$Y;delta<-data1$delta;id<-data1$id;X<-cbind(data1$Z.1,data1$Z.2,data1$Z.3)
  Z<-cbind(data1$Z.2,data1$Z.3);n<-length(as.numeric(table(id)));K<-length(id)/n


  C.11<-diag(1,K); C.12<-matrix(1,K,K)-diag(1,K)

  #############The initial value

  para.init<-aftgee(Surv(Y,delta)~0+Z.1+Z.2+Z.3,id =id,data=data1,corstr="ind",B =2,binit = "lm")$coef.res

  ##################### GIFAI auxiliary information

  CovariAI<-CovariAI.f(para=para.init,
                       d=0,ZZ=X,ZZAI=Z,TT=Y,delta=delta,Weight=Weight,n,K,gamma=gamma.e)

  QIFAI<-function(para2){
    U1<-Sn.f(para=para2,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.11)
    U2<-Sn.f(para=para2,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.12)
    U3<-Sn.f(para=gamma.e,ZZ=Z,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.11)
    U<-rbind(U1,U2,U3)
    out<-t(U)%*%ginv(CovariAI)%*%U
    return(out)
  }
  est.AI<-optim(par = para.init,fn=QIFAI,
                method="Nelder-Mead")$par

  #####Variance estimation

  Gamma.AI<-CovariAI.f(para=est.AI,
                       d=0,ZZ=X,ZZAI=Z,TT=Y,delta=delta,Weight=Weight,n,K,gamma=gamma.e)
  Phi.value<-rbind(Sn.f(para=est.AI,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.11),
                   Sn.f(para=est.AI,ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.12))

  ##estimate the D

  B.times<-boots.num
  eta.AI<-rmvnorm(B.times,rep(0,length(est.AI)),diag(1,length(est.AI)))

  theta.tilde<-matrix(est.AI,B.times,length(est.AI),byrow = TRUE)+n^(-1/2)*eta.AI

  B.formula1<-t(sapply(1:B.times,function(s){return(n^(0.5)*
    rbind(Sn.f(para=theta.tilde[s,],ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.11),
          Sn.f(para=theta.tilde[s,],ZZ=X,TT=Y,delta=delta,Weight=Weight,n,K,MA=C.12))
    -n^(0.5)*Phi.value
  )}))# B.times:(p+q)

  B.formula2<-ginv(t(eta.AI)%*%eta.AI)%*%t(eta.AI)
  D<-t(sapply(1:dim(B.formula1)[2],function(s){return(B.formula2%*%B.formula1[,s])}))

  variance.AI<-n^(-1)*ginv(t(rbind(D,matrix(0,dim(Z)[2],dim(D)[2])))%*%ginv(Gamma.AI)%*%
    rbind(D,matrix(0,dim(Z)[2],dim(D)[2])))

  se.AI<-sqrt(diag(variance.AI))


  return(c(est.AI,se.AI))

}










